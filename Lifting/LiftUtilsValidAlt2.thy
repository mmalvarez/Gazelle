theory LiftUtilsValidAlt
 imports  "../MergeableTc/MergeableInstances" "../MergeableTc/MergeableAList"
begin

(* lifting' is used for syntax *)
type_synonym ('a, 'b) lifting' = "('b \<Rightarrow> 'a)"

(* key abstraction used to lift semantics into larger types *)
record ('syn, 'a, 'b) lifting =
  LIn :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)"
  LOut :: "('syn \<Rightarrow> 'b \<Rightarrow> 'a)"
  LBase :: "'b"

definition LNew :: "('syn, 'a, 'b, 'z) lifting_scheme \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b" where
"LNew l s a =
  LIn l s a (LBase l)"

declare LNew_def [simp]

(* idea: OutS captures set of things we can project
   reset resets inner data back to base but does not change anything else *)
record ('syn, 'a, 'b) liftingv = "('syn, 'a, 'b) lifting" +
  LOutS :: "'syn \<Rightarrow> 'b set"
  LReset :: "'b \<Rightarrow> 'b"

(*
record ('syn, 'a, 'b) liftingvm = "('syn, 'a, 'b) liftingv" +
  LMgS :: "'syn \<Rightarrow> 'b \<Rightarrow> 'b set"
*)

(* idea: capture how we need to weaken a predicate after a merge *)
record ('syn, 'a, 'b) liftingm = "('syn, 'a, 'b) lifting" +
  LMgS :: "'syn \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow>
           ('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)"

(* let's see if this is more ergonomic *)
declare lifting.cases [simp]
declare liftingv.cases [simp]

definition l_adapt  ::
  "('syn1 \<Rightarrow> 'syn2) \<Rightarrow>
   ('syn2, 'a, 'b) lifting \<Rightarrow>
   ('syn1, 'a, 'b) lifting" where
"l_adapt f t =
  \<lparr> LIn = (\<lambda> s a b . LIn t (f s) a b)
  , LOut = (\<lambda> s b . LOut t (f s) b)
  , LBase = LBase t \<rparr>"

declare l_adapt_def [simp]

definition l_map ::
  "('x, 'a, 'b) lifting \<Rightarrow>
    ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"l_map l sem syn st =
  (LIn l syn (sem syn (LOut l syn st)) st)"

declare l_map_def [simp]

definition l_map_s ::
    "('a1, 'b1) lifting' \<Rightarrow>
     ('a1, 'a2, 'b2, 'z) lifting_scheme \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"l_map_s l' l sem syn st =
  (LIn l (l' syn) (sem (l' syn) (LOut l (l' syn) st)) st)"

declare l_map_s_def [simp]

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
   ('a1, 'a2, 'b2, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2)" where
"l_unmap_s l' l sem syn st =
  (let syn' = (SOME x . l' x = syn) :: 'b1 in
  (LOut l syn (sem syn' (LNew l syn st))))"

declare l_unmap_s_def [simp]

definition l_pred :: "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred t P =
  (\<lambda> s b . P s (LOut t s b))"

declare l_pred_def [simp]

definition l_unpred :: "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool)" where
"l_unpred t P =
  (\<lambda> s a . P s (LNew t s a))"

declare l_unpred_def [simp]

definition l_pred_step ::
  "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('x \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step l P s st1 st2 =
        (P s (LOut l s st1) (LOut l s st2))"

(* idea: when contained data is the same,
   result's contained data is the same. *)
definition can_unmap ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a1, 'a2, 'b2, 'z) lifting_scheme \<Rightarrow>
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
(*
definition l_unpred_step ::
  "('x, 'a, 'b) lifting \<Rightarrow>
   ('x \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool)" where
"l_unpred_step l P s st1 st2 =
        (P s (LNew l s st1) (LIn l s st2 (LNew l s st1)))"
*)
 

definition l_pred_step_s ::
  "('s1, 's2) lifting' \<Rightarrow>
   ('s1, 'b1, 'b2, 'z) lifting_scheme \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool) \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step_s l1 l2 P syn st1 st2 =
   (P (l1 syn) (LOut l2 (l1 syn) st1) (LOut l2 (l1 syn) st2))"

definition l_unpred_step_s ::
  "('s1, 's2) lifting' \<Rightarrow>
   ('s1, 'b1, 'b2, 'z) lifting_scheme \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool)" where
"l_unpred_step_s l1 l2 P syn st1 st2 =
   (\<forall> syn' . l1 syn' = syn \<longrightarrow>
     (P syn' (LNew l2 syn st1) (LIn l2 syn st2 (LNew l2 syn st1))))"

(* if we have a pord, do we want to allow out to return more information?
   i think maybe not - the goal of liftings is to inject exactly what we want... (?)
 *)
(* another question. will LIn be in the "OutS" set even if given b isn't?
   i think the answer is yes - this lifting is specific to the 'a-data *)
definition lifting_valid :: "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow> bool" where
"lifting_valid l =
  (\<forall> s a b . LOut l s (LIn l s a b) = a)"

lemma lifting_valid_intro :
  assumes H1 : "\<And> s a b . LOut l s (LIn l s a b) = a"
  shows "lifting_valid l"
  using H1 
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_unfold1 :
  assumes H : "lifting_valid l"
  shows "LOut l s (LNew l s a) = a"
  using H by (auto simp add:lifting_valid_def)

lemma lifting_valid_unfold2 :
  assumes H : "lifting_valid l"
  shows "LOut l s (LIn l s a b) = a"
  using H by (auto simp add:lifting_valid_def)


definition liftingv_valid :: "('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow> bool" where
"liftingv_valid l =
  ((lifting_valid l) \<and>
   (\<forall> s a b . LIn l s a b \<in> LOutS l s) \<and>
   (\<forall> s b . 
    b \<in> LOutS l s \<longrightarrow>
    b <[ LIn l s (LOut l s b) b))"

lemma liftingv_valid_intro :
  assumes H1 : "lifting_valid l"
  assumes H2 : "\<And> s a b . LIn l s a b \<in> LOutS l s"
  assumes H3 : "\<And> s b . b \<in> LOutS l s \<longrightarrow> (b <[ LIn l s (LOut l s b) b)"
  shows "liftingv_valid l"
  using H1 H2 H3 by (auto simp add:liftingv_valid_def)

lemma liftingv_valid_unfold1 :
  assumes H : "liftingv_valid l"
  shows "lifting_valid l" using H by (auto simp add: liftingv_valid_def)

lemma liftingv_valid_unfold2' :
  assumes Hv : "liftingv_valid l"
  shows "LNew l s a \<in> LOutS l s"
  using Hv by (auto simp add: liftingv_valid_def)

lemma liftingv_valid_unfold2 :
  assumes Hv : "liftingv_valid l"
  shows "LIn l s a b \<in> LOutS l s"
  using Hv by (auto simp add:liftingv_valid_def)

lemma liftingv_valid_unfold3 :
  assumes Hv : "liftingv_valid l"
  assumes H : "b \<in> LOutS l s"
  shows "b <[ LIn l s (LOut l s b) b"
  using Hv H by (auto simp add:liftingv_valid_def)

definition liftingvb_valid :: "('x, 'a, 'b :: Pordb, 'z) liftingv_scheme \<Rightarrow> bool" 
where
"liftingvb_valid l =  
  ((liftingv_valid l) \<and>
   LBase l = \<bottom>)"

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

lemma l_adapt_valid :
  fixes f :: "('x1 \<Rightarrow> 'x2)"  
  fixes t :: "('x2, 'a, 'b) lifting"
  assumes H : "lifting_valid t"
  shows "lifting_valid (l_adapt f t)" using H
  by(auto simp add:lifting_valid_def)
declare[[show_types]]

lemma l_pred_step_s_map_s :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) lifting_scheme"
  assumes Hv : "lifting_valid l2"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x1 x2' = x2"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step_s l1 l2 P (x1') (x2') (l_map_s l1 l2 f (x1') (x2'))"
  using Hsyn Hsem HP lifting_valid_unfold2[OF Hv] 
  by(cases l2; auto simp add:l_pred_step_s_def)

definition LFlatten ::
  "('x, 'a, 'b) lifting \<Rightarrow> 'x \<Rightarrow> 'b \<Rightarrow> 'b" where
"LFlatten l s b =
  LNew l s (LOut l s b)"

(* I'm worried this is too restrictive.
   Should we use ordering/monotonicity somehow? *)
(* after thinking about this some more.
   i think we need to have a separate way of characterizing
   what happens during merges.
   i think we should get predicates for which "can_unpred"
   holds if we do it right (?)
   well, maybe i was thinking about predicates capturing one step.
   what about multiple steps?
   e.g. how does multi step semantics of one language relate to
   multiple steps of composition?
   i think i will need to put together 

*)
definition can_unpred ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   bool" where
"can_unpred l' l P =
  (\<forall> syn syn' st1 st2 st'1 st'2.
    l' syn = l' syn' \<longrightarrow>
    LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<longrightarrow>
    LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<longrightarrow>
    st'2 <[ st2 \<longrightarrow>
    P syn st1 st'2 \<longrightarrow> P syn' st'1 st2)"
(* should roles of st'2 and st2 be reversed? *)

lemma can_unpred_intro :
  assumes H : 
    "\<And> syn syn' st1 st2 st'1 st'2 .
      l' syn = l' syn' \<Longrightarrow>
      LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<Longrightarrow>
      LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<Longrightarrow>
      st'2 <[ st2 \<Longrightarrow>
      P syn st1 st'2 \<Longrightarrow> P syn' st'1 st2"
  shows "can_unpred l' l P"
  using H
  unfolding can_unpred_def
  by blast

lemma can_unpred_unfold :
  assumes H : "can_unpred l' l P"
  assumes H1 : "l' syn = l' syn'"
  assumes H2 : "LOut l (l' syn) st1 = LOut l (l' syn') st'1"
  assumes H3 : "LOut l (l' syn) st2 = LOut l (l' syn') st'2 "
  assumes H4 : "st'2 <[ st2"
  assumes Hl : "P syn st1 st'2"
  shows "P syn' st'1 st2"
  using H H1 H2 H3 H4 Hl
  unfolding can_unpred_def
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

declare [[show_types = false]]
lemma l_unpred_step_s_unmap_s  :
  assumes Hv : "liftingv_valid l2"
  assumes Hx2' : "x2' \<in> LOutS l2 x1"
  assumes Hpres : "pres_LOutS l1 l2 f'"
  assumes Hunmap : "can_unmap l1 l2 f'"
  assumes Hunpred : "can_unpred l1 l2 P'"
  assumes H: "\<And> x1'' . l1 x1'' = x1 \<Longrightarrow> P' x1'' x2' (f' x1'' x2')"
  shows "l_unpred_step_s l1 l2 P' x1 (LOut l2 x1 x2') (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2'))"
  unfolding l_unpred_step_s_def l_unmap_s_def Let_def
proof(rule allI; rule impI)
  fix syn'
  assume Hsyn' : "l1 syn' = x1"

  have Syn : "l1 (SOME x. l1 x = x1) = x1"
    by(rule Hilbert_Choice.someI; rule Hsyn')

  have Syn_eq : "l1 (SOME x. l1 x = x1) = l1 syn'" using Hsyn' Syn by simp

  have Eq1 : "LOut l2 (l1 syn') (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 syn') x2'"
    using Hsyn' lifting_valid_unfold1[OF liftingv_valid_unfold1[ OF Hv]] by auto

  have Eq2 :
"LOut l2 (l1 syn') (LIn l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LIn l2 x1 (LOut l2 x1 x2') (LBase l2)))) (LIn l2 x1 (LOut l2 x1 x2') (LBase l2))) =
  (LOut l2 x1 (f' (SOME x. l1 x = x1) (LIn l2 x1 (LOut l2 x1 x2') (LBase l2))))"
    using lifting_valid_unfold2[OF liftingv_valid_unfold1[OF Hv], of "l1 syn'"] Hsyn'
    by(auto)

  have Eq3 :
"LOut l2 (l1 (SOME x. l1 x = x1)) (f' (SOME x. l1 x = x1) (LIn l2 x1 (LOut l2 x1 x2') (LBase l2))) = LOut l2 (l1 syn') (f' syn' x2')"
  proof(rule can_unmap_unfold[OF Hunmap Syn_eq])
    show "LOut l2 (l1 (SOME x. l1 x = x1)) (LIn l2 x1 (LOut l2 x1 x2') (LBase l2)) = LOut l2 (l1 syn') x2'"
      using Syn Hsyn' lifting_valid_unfold2[OF liftingv_valid_unfold1[OF Hv], of "l1 (SOME x. l1 x = x1)"]
      by(simp)
  qed

  have Eq3' :
"LOut l2 x1 (f' (SOME x. l1 x = x1) (LIn l2 x1 (LOut l2 x1 x2') (LBase l2))) = LOut l2 (l1 syn') (f' syn' x2')"
    using Eq3 Syn by simp

  show "P' syn' (LNew l2 x1 (LOut l2 x1 x2')) 
             (LIn l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))))
                (LNew l2 x1 (LOut l2 x1 x2')))" 
    unfolding  Eq3' 

  proof(rule can_unpred_unfold[OF Hunpred refl sym[OF Eq1] _ _ H[OF Hsyn']])
    show "LOut l2 (l1 syn') (LIn l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))) (LNew l2 x1 (LOut l2 x1 x2'))) = LOut l2 (l1 syn') (f' syn' x2')"
      unfolding LNew_def Eq3 Eq2 Eq3 Eq3' 
      using lifting_valid_unfold2[OF liftingv_valid_unfold1[OF Hv]] unfolding Hsyn'
      by(auto)
  next
    have Hx2'_alt : "x2' \<in> LOutS l2 (l1 syn')" using Hx2' Hsyn' by auto
    have F'_LOutS : "f' syn' x2' \<in> LOutS l2 x1" using pres_LOutS_unfold[OF Hpres Hx2'_alt] unfolding Hsyn' by auto
    show "f' syn' x2' <[ LIn l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))))
             (LNew l2 x1 (LOut l2 x1 x2'))"
      unfolding Syn LNew_def Eq3'
      using liftingv_valid_unfold3[OF Hv F'_LOutS] unfolding Hsyn'
(*  proof(rule can_unpred_unfold[OF Hunpred refl Eq1 _ H[OF Hsyn']]) *)
(*  proof(rule can_unpred_unfold[OF Hunpred refl sym[OF Eq1] _ _ H[OF Hsyn']]) *)
(*
proof(rule can_unpred_unfold[OF Hunpred refl])
    show "LOut l2 (l1 syn') (f' syn' x2') =
          LOut l2 (l1 syn') (LIn l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))) (LNew l2 x1 (LOut l2 x1 x2')))"
      using Eq2 Eq3'
      by(simp)
  next
    have OutS : "f' syn' (LNew l2 x1 (LOut l2 x1 x2')) \<in> LOutS l2 x1" 
      using pres_LOutS_unfold[OF Hpres, of "(LNew l2 x1 (LOut l2 x1 x2'))" syn'] Hx2'
      unfolding Hsyn' sorry (* TODO *)
    show "f' syn' x2' <[
    LIn l2 x1
     (LOut l2 x1 (f' (SOME x::'e. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))))
     (LNew l2 x1 (LOut l2 x1 x2'))"
      using liftingv_valid_unfold3[ OF Hv OutS]  Syn Eq3
(* need something extra here? don't know how to pass through function *)
      apply(auto)
  qed
*)
qed

(* need an assumption about equality of the translated syntax elements. *)
lemma lift_lower_asm1 :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) lifting_scheme"
  assumes Hv : "lifting_valid l2"
  shows "can_unmap l1 l2 (l_map_s l1 l2 f)"
proof(rule can_unmap_intro)
    fix b1_1 b1_2 :: 'b1
    fix b2_1 b2_2 :: 'b2  
    assume Hsyn : "l1 b1_1 = l1 b1_2"
    assume Heq : " LOut l2 (l1 b1_1) b2_1 = LOut l2 (l1 b1_2) b2_2"
    show " LOut l2 (l1 b1_1) (l_map_s l1 l2 f b1_1 b2_1) =
           LOut l2 (l1 b1_2) (l_map_s l1 l2 f b1_2 b2_2)"
      unfolding l_map_s_def using Hsyn Heq lifting_valid_unfold2[OF Hv]
      by(simp)
  qed

lemma lift_lower_asm2 :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) lifting_scheme"
  assumes Hv : "lifting_valid l2"
  shows "can_unpred l1 l2 (l_pred_step_s l1 l2 P)"
proof(rule can_unpred_intro)
  fix syn syn' :: 'b1
  fix st1 st2 st'1 st'2 :: 'b2
  assume Hsyn : "l1 syn = l1 syn'"
  assume H1 : "LOut l2 (l1 syn) st1 = LOut l2 (l1 syn') st'1"
  assume H2 : "LOut l2 (l1 syn) st2 = LOut l2 (l1 syn') st'2"
  show "l_pred_step_s l1 l2 P syn st1 st2 = l_pred_step_s l1 l2 P syn' st'1 st'2"
    unfolding l_pred_step_s_def
    using Hsyn H1 H2 by(simp)
qed

(* OK, so to put this together. we need
   - inverse theorem (pred/map)
*)
declare[[show_types = false]]
lemma lift_lower :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) lifting_scheme"
  assumes Hv : "lifting_valid l2"
  assumes H : "P x1 x2 (f x1 x2)"
  shows
    "l_unpred_step_s l1 l2 (l_pred_step_s l1 l2 P) x1 x2
                           (l_unmap_s l1 l2 (l_map_s l1 l2 f) x1 x2)"
proof-
  have "l_unpred_step_s l1 l2 (l_pred_step_s l1 l2 P) x1 (LOut l2 x1 (LNew l2 x1 x2))
       (l_unmap_s l1 l2 (l_map_s l1 l2 f) x1 (LOut l2 x1 (LNew l2 x1 x2)))"
proof(rule l_unpred_step_s_unmap_s[OF Hv lift_lower_asm1[OF Hv] lift_lower_asm2[OF Hv], of l1 x1 P])
    fix x1'' :: 'b1
    assume Hinner : "l1 x1'' = x1"
    show "l_pred_step_s l1 l2 P x1'' (LNew l2 x1 x2) (l_map_s l1 l2 f x1'' (LNew l2 x1 x2))"
    proof(rule l_pred_step_s_map_s[OF Hv, 
                                of l1 x1'' x1 "LNew l2 x1 x2" x2, 
                                OF Hinner ])
      show "LOut l2 x1 (LNew l2 x1 x2) = x2"
        using lifting_valid_unfold1[OF Hv] by auto
    next
      show "P x1 x2 (f x1 x2)" using H by auto
    qed
  qed

  thus
"l_unpred_step_s l1 l2 (l_pred_step_s l1 l2 P) x1 x2 (l_unmap_s l1 l2 (l_map_s l1 l2 f) x1 x2)"
    using lifting_valid_unfold1[OF Hv] by auto
qed

(* have:
LOut l2 (l1 syn') (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 x1 x2'
*)
(*    apply(rule can_unpred_unfold1[OF Hunpred, of "(SOME x. l1 x = x1)"]) *)
(*
using H Hl2  Hx2' can_unmap_unfold[OF Hunmap]
  liftingv_valid_unfold2[OF Hv]
  liftingv_valid_unfold3[OF Hv]
  liftingv_valid_unfold4[OF Hv Hx2']
*)
  


(* TO DOs:
  - pred_lift_s valid
  - pred_unlift_s valid
  - relating lift and unlift for functions
*)

end