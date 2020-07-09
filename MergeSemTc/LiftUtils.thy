theory LiftUtils imports  "../MergeableTc/MergeableInstances" 

begin

(* we cannot always get a b out, so in order to
   be able to compose we need 1 and 2-argument versions
   of LIn. This feels ugly but I will try to revisit this
   later if I have time. *)

(* lifting' is used for syntax *)
type_synonym ('a, 'b) lifting' = "('b \<Rightarrow> 'a)"

record ('a, 'b) lifting =
  LIn1 :: "('a \<Rightarrow> 'b)"
  LIn2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'b)"
  LOut :: "('b \<Rightarrow> 'a)"

(* idea: tailor the exact lifting we use based on the syntax.
   this is useful if e.g. we want to use different priority values
   in different cases *)
record ('syn, 'a, 'b) lifting_gen =
  LIn1_g :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b)"
  LIn2_g :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)"
  LOut_g :: "('b \<Rightarrow> 'a)"

definition id_l ::
  "('a, 'a) lifting" where
"id_l =
  \<lparr> LIn1 = id
  , LIn2 = (\<lambda> x y . id x)
  , LOut = id\<rparr>" 

definition id_l' ::
  "('a, 'a) lifting'" where
  "id_l' = id"

definition id_lg ::
  "('x, 'a, 'a) lifting_gen" where
"id_lg =
  \<lparr> LIn1_g = (\<lambda> s x . x)
  , LIn2_g = (\<lambda> s x y . x)
  , LOut_g = id\<rparr>" 

definition triv_l ::
  "('a, 'b) lifting \<Rightarrow> ('a, 'b md_triv) lifting" where
"triv_l t =
  \<lparr> LIn1 = mdt o (LIn1 t)
  , LIn2 = (\<lambda> a b . (case b of (mdt b') \<Rightarrow> (mdt ( (LIn2 t a b')))))
  , LOut = (case_md_triv (LOut t))\<rparr>"

definition triv_lg ::
  "('x, 'a, 'b) lifting_gen \<Rightarrow> ('x, 'a, 'b md_triv) lifting_gen" where
"triv_lg t =
  \<lparr> LIn1_g = (\<lambda> s x . mdt ( LIn1_g t s x))
  , LIn2_g = (\<lambda> s a b . (case b of (mdt b') \<Rightarrow> (mdt ( (LIn2_g t s a b')))))
  , LOut_g = (case_md_triv (LOut_g t))\<rparr>"

definition triv_l' ::
  "('a, 'b) lifting' \<Rightarrow> ('a, 'b md_triv) lifting'" where
"triv_l' t' =
  (case_md_triv t')"

definition option_l ::
  "('a, 'b) lifting \<Rightarrow>
   ('a, 'b option) lifting" where
"option_l t =
  \<lparr> LIn1 = Some o (LIn1 t)
  , LIn2 = (\<lambda> a b . (case b of None \<Rightarrow> Some (LIn1 t a)
                    | Some b' \<Rightarrow> Some (LIn2 t a b')))
  , LOut = case_option undefined (LOut t) \<rparr>"

definition option_l' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a, 'b option) lifting'" where
"option_l' t =
  case_option undefined t "

definition prio_l ::
  "nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow>
  ('a, 'b) lifting \<Rightarrow>
  ('a, 'b md_prio) lifting" where
"prio_l n f t =
  \<lparr> LIn1 = mdp n o (LIn1 t)
  , LIn2 = (\<lambda> a p . (case p of
                mdp m b \<Rightarrow> mdp (f m) (LIn2 t a b)))
  , LOut =
      (\<lambda> p . (case p of
              mdp m b \<Rightarrow> LOut t b))\<rparr>"

definition prio_l' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a, 'b md_prio) lifting'" where
"prio_l' t =
  (\<lambda> p . (case p of
              mdp m b \<Rightarrow> t b))"

definition prio_l_keep :: "('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_keep =
  prio_l 0 id"

definition prio_l_inc :: "('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_inc =
  prio_l 0 (\<lambda> x . 1 + x)"

definition prio_l_const :: "nat \<Rightarrow> ('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_const n =
  prio_l n (\<lambda> _ . n)"

definition prio_l_zero ::
"('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_zero =
  prio_l_const 0"

definition prio_l_one ::
"('a, 'b) lifting \<Rightarrow> ('a, 'b md_prio) lifting" where
"prio_l_one =
  prio_l_const 1"


definition fst_l ::
  "('a, 'b1) lifting \<Rightarrow>
   ('a, 'b1 * ('b2 :: Pordb)) lifting" where
"fst_l t =
  \<lparr> LIn1 = (\<lambda> x . (LIn1 t x, \<bottom>))
  , LIn2 = (\<lambda> a b . (case b of
                      (b1, b2) \<Rightarrow> ((LIn2 t a b1), \<bottom>)))
  , LOut = (\<lambda> x . (LOut t (fst x))) \<rparr>"

definition snd_l ::
  "('a, 'b2) lifting \<Rightarrow>
   ('a, ('b1 :: Pordb) * ('b2)) lifting" where
"snd_l t =
  \<lparr> LIn1 = (\<lambda> x . (\<bottom>, LIn1 t x))
  , LIn2 = (\<lambda> a b . (case b of
                      (b1, b2) \<Rightarrow> (\<bottom>, (LIn2 t a b2))))
  , LOut = (\<lambda> x . (LOut t (snd x))) \<rparr>"

definition fst_l' ::
  "('a, 'b1) lifting' \<Rightarrow>
   ('a, 'b1 * 'b2) lifting'" where
"fst_l' t =
  (\<lambda> x . t (fst x))"

definition snd_l' ::
  "('a, 'b2) lifting' \<Rightarrow>
   ('a, 'b1 * 'b2) lifting'" where
"snd_l' t =
  (\<lambda> x . (t (snd x)))"

(* unclear to me how useful this is *)
definition prod_l ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2) lifting" where
"prod_l t1 t2 =
  \<lparr> LIn1 = 
    (\<lambda> x . (case x of (x1, x2) \<Rightarrow> (LIn1 t1 x1, LIn1 t2 x2)))
  , LIn2 =
    (\<lambda> a b . (case a of (a1, a2) \<Rightarrow>
                (case b of (b1, b2) \<Rightarrow>
                  (LIn2 t1 a1 b1, LIn2 t2 a2 b2))))
  , LOut =
    (\<lambda> x . (case x of (x1, x2) \<Rightarrow>
              (LOut t1 x1, LOut t2 x2)))\<rparr>"

definition prod_l' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting' \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2) lifting'" where
"prod_l' t1 t2 =
  (\<lambda> x . (case x of (x1, x2) \<Rightarrow> (t1 x1, t2 x2)))"

(* this may not be that useful
   also, do we want this to be more like option? (or prod_lm?) *)
definition sum_l ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 + 'a2, 'b1 + 'b2) lifting" where
"sum_l t1 t2 =
  \<lparr> LIn1 = 
    (\<lambda> x . (case x of Inl x1 \<Rightarrow> Inl (LIn1 t1 x1) | Inr x2 \<Rightarrow> Inr (LIn1 t2 x2)))
  , LIn2 =
    (\<lambda> a b . (case a of
                Inl a1 \<Rightarrow>
                  (case b of Inl b1 \<Rightarrow> Inl (LIn2 t1 a1 b1)
                             | Inr _ \<Rightarrow> Inl (LIn1 t1 a1))
                | Inr a2 \<Rightarrow>
                  (case b of Inl _ \<Rightarrow> Inr (LIn1 t2 a2)
                             | Inr b2 \<Rightarrow> Inr (LIn2 t2 a2 b2))))
  , LOut =
    (\<lambda> x . (case x of 
              Inl x1 \<Rightarrow> Inl (LOut t1 x1)
              | Inr x2 \<Rightarrow> Inr (LOut t2 x2))) \<rparr>"

definition sum_l_inl ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a1, 'b1 + 'b2) lifting" where
"sum_l_inl t =
  \<lparr> LIn1 = 
    (\<lambda> x . Inl (LIn1 t x))
  , LIn2 =
    (\<lambda> a b . (case b of
                Inl b' \<Rightarrow> Inl (LIn2 t a b')
                | Inr _ \<Rightarrow> Inl (LIn1 t a)))
  , LOut =
    (\<lambda> x . (case x of 
              Inl x1 \<Rightarrow> LOut t x1
              | Inr x2 \<Rightarrow> undefined)) \<rparr>"

definition sum_l_inr ::
  "('a1, 'b2) lifting \<Rightarrow>
   ('a1, 'b1 + 'b2) lifting" where
"sum_l_inr t =
  \<lparr> LIn1 = 
    (\<lambda> x . Inr (LIn1 t x))
  , LIn2 =
    (\<lambda> a b . (case b of
                Inr b' \<Rightarrow> Inr (LIn2 t a b')
                | Inl _ \<Rightarrow> Inr (LIn1 t a)))
  , LOut =
    (\<lambda> x . (case x of 
              Inr x1 \<Rightarrow> LOut t x1
              | Inl x2 \<Rightarrow> undefined)) \<rparr>"


definition sum_l' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting' \<Rightarrow>
   ('a1 + 'a2, 'b1 + 'b2) lifting'" where
"sum_l' t1 t2 =
  (\<lambda> x .
    (case x of
      Inl x1 \<Rightarrow> Inl (t1 x1)
      | Inr x2 \<Rightarrow> Inr (t2 x2)))"

(* this biases toward the first component. *)
(*
definition prod_lm ::
  "('a1, 'b :: Mergeableb) lifting \<Rightarrow>
   ('a2, 'b) lifting \<Rightarrow>
   ('a1 * 'a2, 'b) lifting" where
"prod_lm t1 t2 =
  \<lparr> LIn1 = 
    (\<lambda> x . (case x of (x1, x2) \<Rightarrow> [^LIn1 t1 x1, LIn1 t2 x2^]))
  , LIn2 =
    (\<lambda> a b . (case a of (a1, a2) \<Rightarrow>
                  [^LIn2 t1 a1 b, LIn2 t2 a2 b^]))
  , LOut =
    (\<lambda> x . (case (LOut t1 x) of
              None \<Rightarrow> None
              | Some x1' \<Rightarrow>
                (case (LOut t2 x) of
                  None \<Rightarrow> None
                  | Some x2' \<Rightarrow> Some (x1', x2')))) \<rparr>"
*)
definition l_map ::
  "('a, 'b) lifting \<Rightarrow>
   ('a \<Rightarrow> 'a) \<Rightarrow>
   ('b \<Rightarrow> 'b)" where
"l_map l sem b =
  (LIn2 l (sem (LOut l b)) b)"

definition l_map2 ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"l_map2 l1 l2 sem syn st =
  (LIn2 l2 (sem (LOut l1 syn) (LOut l2 st)) st)"

definition l_map2' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"l_map2' l1 l2 sem syn st =
    (LIn2 l2 (sem (l1 syn) (LOut l2 st)) st)"


(* is False the right default here? *)
definition l_pred :: "('a, 'b) lifting \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where
"l_pred t P =
  (\<lambda> b . P (LOut t b))"

definition l_pred' :: "('a, 'b) lifting' \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where
"l_pred' t P =
  (\<lambda> b . P (t b))"


(* we also want 2 notions of lifting preds over functions
   (1 for semantics only; 1 for syntax) *)

definition l_pred_step ::
  "('a, 'b) lifting \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step l P st1 st2 =
        (P (LOut l st1) (LOut l st2))"

definition l_pred_step' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step' l P st1 st2 =
        (P (l st1) (l st2))"

(* Is False the right default for "couldn't find syntax"?
   In this case I think so... *)
definition l_pred_step2 ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step2 l1 l2 P syn st1 st2 =
  ( P (LOut l1 syn) (LOut l2 st1) (LOut l2 st2))"

definition l_pred_step2' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step2' l1 l2 P syn st1 st2 =
   (P (l1 syn) (LOut l2 st1) (LOut l2 st2))"

(* probably less useful *)
(*
definition l_pred_step2'' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting' \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step2'' l1 l2 P syn st1 st2 =
  (case l1 syn of
    None \<Rightarrow> False
    | Some syn' \<Rightarrow>
       (case l2 st1 of
          None \<Rightarrow> False
          | Some st1' \<Rightarrow>
            (case l2 st2 of
              None \<Rightarrow> False
              | Some st2' \<Rightarrow> P syn' st1' st2')))"
*)

definition l_val ::
  "('a, 'b) lifting \<Rightarrow>
   'a \<Rightarrow> 'b" where
"l_val l a = LIn1 l a"

(* I am not sure if this one is useful. *)
(*
definition l_pred_sem ::
  "('a, 'b) lifting \<Rightarrow>
   (('a \<Rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow>
   (('b \<Rightarrow> 'b) \<Rightarrow> bool)" where
"l_pred_sem l P f =
  (\<forall> g :: "'a \<Rightarrow> 'a" . 
     P g \<longrightarrow> (\<forall> x . \<exists> x' . LOut l (g x) = Some x')) \<and>
  P (\<lambda> a . (case LOut l (sem (LIn1 l a)) of Some a' \<Rightarrow> a'))
*)

(* what we want:
   Lout (Lin1 a) = Some a
   Lout (Lin2 a b) = Some a
   Lout b = Some a \<longrightarrow> Lin2 a b = b
  this last one doesn't really work - see for instance prio
*)

(* for things with \<bottom>
   we could also have LIn1 l a = LIn2 l a \<bottom>
   this may become useful/necessary at some point
*)
definition lifting_valid ::
  "('a, 'b) lifting \<Rightarrow> bool" where
"lifting_valid l =
 ((\<forall> a .  LOut l (LIn1 l a) = a) \<and>
  (\<forall> a b . LOut l (LIn2 l a b) = a))"

lemma lifting_valid_intro :
  assumes H1 : "\<And> a .  LOut l (LIn1 l a) = a"
  assumes H2 : "\<And> a b . LOut l (LIn2 l a b) = a"
  shows "lifting_valid l"
  using H1 H2
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_unfold1 :
  assumes H : "lifting_valid l"
  shows "LOut l (LIn1 l a) = a"
  using H by (auto simp add:lifting_valid_def)

lemma lifting_valid_unfold2 :
  assumes H : "lifting_valid l"
  shows "LOut l (LIn2 l a b) = a"
  using H by (auto simp add:lifting_valid_def)

(* need to universally quantify over x? *)
(* prove versions for all 4 combinations In1/In2?*)
lemma pred_lift :
  assumes Hv : "lifting_valid l"
  assumes HP : "P x (f x)"
  shows "l_pred_step l P (LIn2 l x b) (l_map l f (LIn2 l x b))"
  using HP lifting_valid_unfold1[OF Hv] lifting_valid_unfold2[OF Hv]
  by(cases l; auto simp add:l_pred_step_def l_map_def split:option.splits)

lemma pred_lift2 :
  assumes Hv1 : "lifting_valid l1"
  assumes Hv2 : "lifting_valid l2"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step2 l1 l2 P (LIn2 l1 x1 y1) (LIn2 l2 x2 y2) (l_map2 l1 l2 f (LIn2 l1 x1 y1) (LIn2 l2 x2 y2))"
  using HP lifting_valid_unfold1[OF Hv1] lifting_valid_unfold2[OF Hv1]
           lifting_valid_unfold1[OF Hv2] lifting_valid_unfold2[OF Hv2]
  by(cases l1; cases l2; auto simp add:l_pred_step2_def l_map2_def split:option.splits)

(* problem: with our syntax thing we can't inject back
   we need some kind of way to solve this *)

(* TODO
we need a version of this that talks out LOut not LIn. *)
lemma pred_lift2' :
  assumes Hv : "lifting_valid l2"
  assumes Hout : "l1 x1' = x1"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step2' l1 l2 P (x1') (LIn2 l2 x2 y2) (l_map2' l1 l2 f (x1') (LIn2 l2 x2 y2))"
  using HP Hout lifting_valid_unfold1[OF Hv] lifting_valid_unfold2[OF Hv]
  by(cases l2; auto simp add:l_pred_step2'_def l_map2'_def split:option.splits)

lemma pred_lift_out2 :
  assumes Hv : "lifting_valid l2"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x2' = x2"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step2' l1 l2 P (x1') (x2') (l_map2' l1 l2 f (x1') (x2'))"
  using Hsyn Hsem HP lifting_valid_unfold2[OF Hv]
  by(cases l2; auto simp add:l_pred_step2'_def l_map2'_def)

lemma id_l_valid : "lifting_valid (id_l)"
  by (rule lifting_valid_intro; auto simp add:id_l_def)

lemma triv_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (triv_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (triv_l l) (LIn1 (triv_l l) a) = a" using lifting_valid_unfold1[OF H]
    by(auto simp add:triv_l_def)
next
  fix a :: 'a
  fix b :: "'b md_triv"
  show "LOut (triv_l l) (LIn2 (triv_l l) a b) = a"
    using lifting_valid_unfold2[OF H]
    by(auto simp add:triv_l_def split:md_triv.splits)
qed

lemma option_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (option_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (option_l l) (LIn1 (option_l l) a) = a" using lifting_valid_unfold1[OF H]
    by(auto simp add:option_l_def)
next
  fix a :: 'a
  fix b :: "'b option"
  show "LOut (option_l l) (LIn2 (option_l l) a b) = a"
    using lifting_valid_unfold2[OF H] lifting_valid_unfold1[OF H]
    by(auto simp add:option_l_def split:option.splits)
qed

(* next up:
   - prio (prove general one)
   - fst, snd *)
lemma prio_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (prio_l n f l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (prio_l n f l) (LIn1 (prio_l n f l) a) = a"
    using lifting_valid_unfold1[OF H] by(auto simp add:prio_l_def)
next
  fix a :: 'a
  fix b :: "'b md_prio"
  show "LOut (prio_l n f l) (LIn2 (prio_l n f l) a b) = a"
    using lifting_valid_unfold2[OF H] by(auto simp add:prio_l_def split:md_prio.splits)
qed

lemma fst_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (fst_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (fst_l l) (LIn1 (fst_l l) a) = a"
    using lifting_valid_unfold1[OF H] by(auto simp add:fst_l_def)
next
  fix a :: 'a
  fix b :: "('b * 'c)"
  show "LOut (fst_l l) (LIn2 (fst_l l) a b) = a"
    using lifting_valid_unfold2[OF H] by(auto simp add:fst_l_def split:prod.splits)
qed

lemma snd_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (snd_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (snd_l l) (LIn1 (snd_l l) a) = a"
    using lifting_valid_unfold1[OF H] by(auto simp add:snd_l_def)
next
  fix a :: 'a
  fix b :: "('c * 'b)"
  show "LOut (snd_l l) (LIn2 (snd_l l) a b) = a"
    using lifting_valid_unfold2[OF H] by(auto simp add:snd_l_def split:prod.splits)
qed

lemma prod_l_valid :
  fixes l1 :: "('a1, 'b1) lifting"
  fixes l2 :: "('a2, 'b2) lifting"
  assumes H1 : "lifting_valid l1"
  assumes H2 : "lifting_valid l2"
  shows "lifting_valid (prod_l l1 l2)"
proof(rule lifting_valid_intro)
  fix a :: "'a1 * 'a2"
  show "LOut (prod_l l1 l2) (LIn1 (prod_l l1 l2) a) = a"
    using lifting_valid_unfold1[OF H1, of "fst a"] lifting_valid_unfold1[OF H2, of "snd a"]
    by(auto simp add:prod_l_def split:prod.splits)
next
  fix a :: "'a1 * 'a2"
  fix b :: "'b1 * 'b2"
  show "LOut (prod_l l1 l2) (LIn2 (prod_l l1 l2) a b) = a"
    using lifting_valid_unfold2[OF H1] lifting_valid_unfold2[OF H2]
    by(auto simp add:prod_l_def split:prod.splits)
qed


definition lifting_valid_gen ::
  "('x, 'a, 'b) lifting_gen \<Rightarrow> bool" where
"lifting_valid_gen l =
 ((\<forall> s a .  LOut_g l (LIn1_g l s a) = a) \<and>
  (\<forall> s a b . LOut_g l (LIn2_g l s a b) = a))"


record ('a, 'b) langcomp =
  Sem1 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  Sem2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

definition sup_pres ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"sup_pres f1 f2 =
 (\<forall> syn :: 'a .
   \<forall> st1 st2 :: 'b .
     has_sup {st1, st2} \<longrightarrow>
     has_sup {f1 syn st1, f2 syn st2})"

lemma sup_pres_unfold :
  fixes f1 f2 :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b)"
  fixes syn :: 'a
  fixes st1 st2 :: 'b
  assumes H : "sup_pres f1 f2"
  assumes Hsup : "has_sup {st1, st2}"
  shows "has_sup {f1 syn st1, f2 syn st2}" using H Hsup
  by(auto simp add:sup_pres_def)

lemma sup_pres_intro :
  fixes f1 f2 :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b)"
  assumes H : "\<And> (syn :: 'a) (st1 :: 'b) (st2 :: 'b) .
                  has_sup {st1, st2} \<Longrightarrow> has_sup {f1 syn st1, f2 syn st2}"
  shows "sup_pres f1 f2" using H
  by(auto simp add:sup_pres_def)

definition sup_pres' ::
  "(('a :: Mergeable) \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"sup_pres' f1 f2 =
 (\<forall> syn1 syn2 :: 'a .
   \<forall> st1 st2 :: 'b .
     has_sup {st1, st2} \<longrightarrow>
     has_sup {syn1, syn2} \<longrightarrow>
     has_sup {f1 syn1 st1, f2 syn2 st2})"

(* LIn1 vs LIn2 *)
definition sup_l ::
  "('a1, ('b :: Mergeable)) lifting \<Rightarrow>
   ('a2, ('b :: Mergeable)) lifting \<Rightarrow>
   bool" where
"sup_l l1 l2 =
  (\<forall> a1 a2 b1 b2 .
    has_sup {LIn1 l1 a1, LIn1 l2 a2} \<and>
    (has_sup {b1, b2} \<longrightarrow> has_sup {LIn2 l1 a1 b1, LIn2 l2 a2 b2}))"

lemma sup_l_intro :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  assumes H1 : "\<And> a1 a2 . has_sup {LIn1 l1 a1, LIn1 l2 a2}"
  assumes H2 : "\<And> a1 a2 b1 b2 . has_sup {b1, b2} \<Longrightarrow> has_sup {LIn2 l1 a1 b1, LIn2 l2 a2 b2}"
  shows "sup_l l1 l2" using H1 H2
  by(auto simp add:sup_l_def)

lemma sup_l_unfold1 :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  assumes H : "sup_l l1 l2"
  shows "has_sup {LIn1 l1 a1, LIn1 l2 a2}"
  using H   by(auto simp add:sup_l_def)

lemma sup_l_unfold2 :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  assumes H : "sup_l l1 l2"
  assumes Hb : "has_sup {b1, b2}"
  shows "has_sup {LIn2 l1 a1 b1, LIn2 l2 a2 b2}"
    using H Hb
  by(auto simp add:sup_l_def)


lemma sup_l_prod_fst :
  fixes l1  :: "('a1, 'b1 :: Mergeableb) lifting"
  fixes l1' :: "('a2, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('a3, 'b2 :: Mergeableb) lifting"
  assumes H : "sup_l l1 l1'"
  shows "sup_l (prod_l l1 l2) (fst_l l1')"
proof(rule sup_l_intro)
  fix a1 :: "('a1 \<times> 'a3)" 
  fix a2 :: "'a2"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub where Hub : "is_sup {LIn1 l1 x1, LIn1 l1' a2} ub"
      using sup_l_unfold1[OF H] Hx
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1 (prod_l l1 l2) a1, LIn1 (fst_l l1') a2} (ub, LIn1 l2 x2)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l l1 l2) a1, LIn1 (fst_l l1') a2}" by (auto simp add:has_sup_def)
next
  fix a1::"'a1 \<times> 'a3"
  fix a2::"'a2"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub1 : "has_sup {y1, z1}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l1 x1 y1, LIn2 l1' a2 z1} ub"
      using sup_l_unfold2[OF H Hub1] Hx Hy Hz
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)

  have "is_sup {LIn2 (prod_l l1 l2) a1 b1, LIn2 (fst_l l1') a2 b2} (ub, LIn2 l2 x2 y2)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l l1 l2) a1 b1, LIn2 (fst_l l1') a2 b2}" by (auto simp add:has_sup_def)
qed

lemma sup_l_inc_zero :
  fixes l1 :: "('a1, 'b :: Mergeableb) lifting"
  fixes l2:: "('a2, 'b :: Mergeableb) lifting"
  shows "sup_l (prio_l_zero l1) (prio_l_inc l2)"
proof(rule sup_l_intro)
  fix a1 :: "'a1"
  fix a2 :: "'a2"

  (* this is kind of a bogus case *)
  have "is_ub {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2} (mdp 1 \<bottom>)"
    by(auto simp add:prio_l_zero_def prio_l_const_def prio_l_def prio_l_inc_def
            has_sup_def is_sup_def is_least_def is_ub_def prio_pleq bot_spec split:md_prio.splits)

  hence 0 : "has_ub {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2}"
    by(auto simp add:has_ub_def)

  obtain lub where
    "is_sup {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2} lub" 
    using complete2[OF 0] by(auto simp add:has_sup_def)
  

  thus "has_sup {LIn1 (prio_l_zero l1) a1, LIn1 (prio_l_inc l2) a2}"
    by(auto simp add:has_sup_def)
next
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b1 :: "'b md_prio"
  fix b2 :: "'b md_prio"
  assume Hsup : "has_sup {b1, b2}"


  have "is_ub {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2} (LIn2 (prio_l_inc l2) a2 b2)"
    by(auto simp add:prio_l_zero_def prio_l_const_def prio_l_def prio_l_inc_def
            leq_refl
            has_sup_def is_sup_def is_least_def is_ub_def prio_pleq bot_spec split:md_prio.splits)

  hence 0 : "has_ub  {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2}"
    by(auto simp add:has_ub_def)

  obtain lub where
    "is_sup {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2} lub"
    using complete2[OF 0] by(auto simp add:has_sup_def)

  thus "has_sup {LIn2 (prio_l_zero l1) a1 b1, LIn2 (prio_l_inc l2) a2 b2}"
    by(auto simp add:has_sup_def)
qed


(* TODO: could generalize this to talk about syntaxes having supremum *)
definition lc_valid :: "('a, 'b :: Mergeable) langcomp \<Rightarrow> bool" where
"lc_valid l =
  sup_pres (Sem1 l) (Sem2 l)"

definition lc_valid' :: "('a :: Mergeable, 'b :: Mergeable) langcomp \<Rightarrow> bool" where
"lc_valid' l =
  sup_pres' (Sem1 l) (Sem2 l)"


lemma lc_valid_intro :
  fixes l :: "('a, 'b :: Mergeable) langcomp"
  assumes H: "\<And> syn st1 st2 . has_sup {st1, st2} \<Longrightarrow> has_sup {Sem1 l syn st1, Sem2 l syn st2}"
  shows "lc_valid l" using H
  by(auto simp add:lc_valid_def sup_pres_def)

lemma lc_valid_unfold :
  fixes l :: "('a, 'b :: Mergeable) langcomp"
  fixes syn :: 'a
  fixes st1 st2 :: 'b
  assumes H : "lc_valid l"
  assumes Hsup : "has_sup {st1, st2}"
  shows "has_sup {Sem1 l syn st1, Sem2 l syn st2}"
  using H Hsup
  by(auto simp add:lc_valid_def sup_pres_def)


(* new issue: we need to deal with the disconnect between
- sup_l: assumes same initial state
- sup_pres: doesn't
*)
lemma sup_l_pres :
  fixes l1 :: "('a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('a2, 'b :: Mergeable) lifting"
  fixes syn_trans1 :: "'syn \<Rightarrow> 'syn1"
  fixes syn_trans2 :: "'syn \<Rightarrow> 'syn2"
  fixes f1 :: "'syn1 \<Rightarrow> 'a1 \<Rightarrow> 'a1"
  fixes f2 :: "'syn2 \<Rightarrow> 'a2 \<Rightarrow> 'a2"
  assumes Hsl : "sup_l l1 l2"
  shows "sup_pres
    (l_map2' syn_trans1 l1 f1)
    (l_map2' syn_trans2 l2 f2)"
proof(rule sup_pres_intro)
  fix syn :: 'syn
  fix st1 :: 'b
  fix st2 :: 'b
  assume Hsup : "has_sup {st1, st2}"
  show "has_sup {l_map2' syn_trans1 l1 f1 syn st1, l_map2' syn_trans2 l2 f2 syn st2}"
    using Hsup sup_l_unfold2[OF Hsl]
    by(auto simp add: l_map2'_def split:option.splits)
qed

definition pcomp :: "('a, 'b :: Mergeable) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomp l a b =
  [^ [^ Sem1 l a b, Sem2 l a b ^], b ^]"

definition pcomp' :: "('a, 'b :: Mergeable) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomp' l a b =
  [^ [^ Sem2 l a b, Sem1 l a b ^], b ^]"

lemma lc_valid_comp :
  fixes l :: "('a, 'b :: Mergeable) langcomp"
  assumes Hv : "lc_valid l"
  shows "pcomp l = pcomp' l"
proof(-)
  have Conc' : "\<And> (b :: 'b ::Mergeable) (a :: 'a) . pcomp l a b = pcomp' l a b"
  proof(-)
    fix a :: 'a
    fix b :: "'b :: Mergeable"
    have "is_sup {b} b"
      using leq_refl by(auto simp add:is_sup_def has_sup_def is_least_def is_ub_def)
    hence 0 : "has_sup {b, b}" by (auto simp add:has_sup_def)
    thus  "pcomp l a b = pcomp' l a b"
      using bsup_comm[OF lc_valid_unfold[OF Hv 0]]
      by(simp add:pcomp_def pcomp'_def)
  qed
  
  thus ?thesis
    by auto
qed


lemma lc_valid_lift :
  assumes Hlc : "lc = \<lparr> Sem1 = (l_map2' syn_trans1 l1 f1)
                      , Sem2 = (l_map2' syn_trans2 l2 f2) \<rparr>" 
  assumes Hsl : "sup_l l1 l2"
  shows "lc_valid lc"
proof(-)
  have "sup_pres
    (l_map2' syn_trans1 l1 f1)
    (l_map2' syn_trans2 l2 f2)" using sup_l_pres[OF Hsl] by auto

  thus "lc_valid lc" by(auto simp add:Hlc lc_valid_def)
qed


lemma sup_l_comm :
  fixes l1  :: "('a1, 'b :: Mergeableb) lifting"
  fixes l2 :: "('a2, 'b :: Mergeableb) lifting"
  assumes H : "sup_l l1 l2"
  shows "sup_l l2 l1"
proof(rule sup_l_intro)
  fix a2 :: 'a2
  fix a1 :: "'a1"
  have "{LIn1 l2 a2, LIn1 l1 a1} = {LIn1 l1 a1, LIn1 l2 a2}" by auto
  thus "has_sup {LIn1 l2 a2, LIn1 l1 a1}" using sup_l_unfold1[OF H, of a1 a2] by auto
next
  fix a2 :: 'a2
  fix a1 :: 'a1
  fix b1 b2 :: 'b
  assume Hs : "has_sup {b1, b2}"

  have "{b2, b1} = {b1, b2}" by auto
  hence Hs' : "has_sup {b2, b1}" using Hs by auto
  have "{LIn2 l1 a1 b2, LIn2 l2 a2 b1} = {LIn2 l2 a2 b1, LIn2 l1 a1 b2}" by auto

  thus "has_sup {LIn2 l2 a2 b1, LIn2 l1 a1 b2}"
    using sup_l_unfold2[OF H Hs', of a1 a2] by auto
qed


end