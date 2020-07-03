theory LiftUtils imports  "../MergeableTc/MergeableInstances" 

begin

(* we cannot always get a b out, so in order to
   be able to compose we need 1 and 2-argument versions
   of LIn. This feels ugly but I will try to revisit this
   later if I have time. *)

type_synonym ('a, 'b) lifting' = "('b \<Rightarrow> 'a option)"

record ('a, 'b) lifting =
  LIn1 :: "('a \<Rightarrow> 'b)"
  LIn2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'b)"
  LOut :: "('b \<Rightarrow> 'a option)"

definition id_l ::
  "('a, 'a) lifting" where
"id_l =
  \<lparr> LIn1 = id
  , LIn2 = (\<lambda> x y . id x)
  , LOut = Some\<rparr>" 

definition id_l' ::
  "('a, 'a) lifting'" where
  "id_l' = Some"


definition triv_l ::
  "('a, 'b) lifting \<Rightarrow> ('a, 'b md_triv) lifting" where
"triv_l t =
  \<lparr> LIn1 = mdt o (LIn1 t)
  , LIn2 = (\<lambda> a b . (case b of (mdt b') \<Rightarrow> (mdt ( (LIn2 t a b')))))
  , LOut = (case_md_triv (LOut t))\<rparr>"

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
  , LOut = case_option None (LOut t) \<rparr>"

definition option_l' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a, 'b option) lifting'" where
"option_l' t =
  case_option None t "

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
              (case (LOut t1 x1) of
                None \<Rightarrow> None
                | Some x1' \<Rightarrow>
                  (case (LOut t2 x2) of
                    None \<Rightarrow> None
                    | Some x2' \<Rightarrow> Some (x1', x2'))))) \<rparr>"

definition prod_l' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting' \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2) lifting'" where
"prod_l' t1 t2 =
  (\<lambda> x . (case x of (x1, x2) \<Rightarrow>
              (case (t1 x1) of
                None \<Rightarrow> None
                | Some x1' \<Rightarrow>
                  (case (t2 x2) of
                    None \<Rightarrow> None
                    | Some x2' \<Rightarrow> Some (x1', x2')))))"


(* this biases toward the first component. *)
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

definition l_map ::
  "('a, 'b) lifting \<Rightarrow>
   ('a \<Rightarrow> 'a) \<Rightarrow>
   ('b \<Rightarrow> 'b)" where
"l_map l sem b =
  (case (LOut l) b of
    None \<Rightarrow> b
    | Some b' \<Rightarrow> 
      (LIn2 l) (sem b') b)"

definition l_map2 ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"l_map2 l1 l2 sem syn st =
  (case (LOut l1) syn of
    None \<Rightarrow> st
    | Some syn' \<Rightarrow> (case (LOut l2) st of
                    None \<Rightarrow> st
                    | Some st' \<Rightarrow>
                      (LIn2 l2 (sem syn' st') st)))"

definition l_map2' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"l_map2' l1 l2 sem syn st =
  (case l1 syn of
    None \<Rightarrow> st
    | Some syn' \<Rightarrow> (case (LOut l2) st of
                    None \<Rightarrow> st
                    | Some st' \<Rightarrow>
                      (LIn2 l2 (sem syn' st') st)))"


(* is False the right default here? *)
definition l_pred :: "('a, 'b) lifting \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where
"l_pred t P =
  (\<lambda> b . (case LOut t b of
          None \<Rightarrow> False
          | Some a \<Rightarrow> P a))"

definition l_pred' :: "('a, 'b) lifting' \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where
"l_pred' t P =
  (\<lambda> b . (case t b of
          None \<Rightarrow> False
          | Some a \<Rightarrow> P a))"


(* we also want 2 notions of lifting preds over functions
   (1 for semantics only; 1 for syntax) *)

definition l_pred_step ::
  "('a, 'b) lifting \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step l P st1 st2 =
  (case (LOut l) st1 of
    None \<Rightarrow> False
    | Some st1' \<Rightarrow> (case (LOut l) st2 of
                    None \<Rightarrow> False
                    | Some st2' \<Rightarrow>
                      (P st1' st2')))"

definition l_pred_step' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step' l P st1 st2 =
  (case l st1 of
    None \<Rightarrow> False
    | Some st1' \<Rightarrow> (case l st2 of
                    None \<Rightarrow> False
                    | Some st2' \<Rightarrow>
                      (P st1' st2')))"

(* Is False the right default for "couldn't find syntax"?
   In this case I think so... *)
definition l_pred_step2 ::
  "('a1, 'b1) lifting \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step2 l1 l2 P syn st1 st2 =
  (case (LOut l1) syn of
    None \<Rightarrow> False
    | Some syn' \<Rightarrow>
       (case (LOut l2) st1 of
          None \<Rightarrow> False
          | Some st1' \<Rightarrow>
            (case (LOut l2) st2 of
              None \<Rightarrow> False
              | Some st2' \<Rightarrow> P syn' st1' st2')))"

definition l_pred_step2' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2 \<Rightarrow> bool) \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step2' l1 l2 P syn st1 st2 =
  (case l1 syn of
    None \<Rightarrow> False
    | Some syn' \<Rightarrow>
       (case (LOut l2) st1 of
          None \<Rightarrow> False
          | Some st1' \<Rightarrow>
            (case (LOut l2) st2 of
              None \<Rightarrow> False
              | Some st2' \<Rightarrow> P syn' st1' st2')))"

(* probably less useful *)
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
 ((\<forall> a .  LOut l (LIn1 l a) = Some a) \<and>
  (\<forall> a b . LOut l (LIn2 l a b) = Some a))"

lemma lifting_valid_intro :
  assumes H1 : "\<And> a .  LOut l (LIn1 l a) = Some a"
  assumes H2 : "\<And> a b . LOut l (LIn2 l a b) = Some a"
  shows "lifting_valid l"
  using H1 H2
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_unfold1 :
  assumes H : "lifting_valid l"
  shows "LOut l (LIn1 l a) = Some a"
  using H by (auto simp add:lifting_valid_def)

lemma lifting_valid_unfold2 :
  assumes H : "lifting_valid l"
  shows "LOut l (LIn2 l a b) = Some a"
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

lemma pred_lift2' :
  assumes Hv : "lifting_valid l2"
  assumes Hout : "l1 x1' = Some x1"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step2' l1 l2 P (x1') (LIn2 l2 x2 y2) (l_map2' l1 l2 f (x1') (LIn2 l2 x2 y2))"
  using HP Hout lifting_valid_unfold1[OF Hv] lifting_valid_unfold2[OF Hv]
  by(cases l2; auto simp add:l_pred_step2'_def l_map2'_def split:option.splits)

lemma id_l_valid : "lifting_valid (id_l)"
  by (rule lifting_valid_intro; auto simp add:id_l_def)

lemma triv_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (triv_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (triv_l l) (LIn1 (triv_l l) a) = Some a" using lifting_valid_unfold1[OF H]
    by(auto simp add:triv_l_def)
next
  fix a :: 'a
  fix b :: "'b md_triv"
  show "LOut (triv_l l) (LIn2 (triv_l l) a b) = Some a"
    using lifting_valid_unfold2[OF H]
    by(auto simp add:triv_l_def split:md_triv.splits)
qed

lemma option_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (option_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (option_l l) (LIn1 (option_l l) a) = Some a" using lifting_valid_unfold1[OF H]
    by(auto simp add:option_l_def)
next
  fix a :: 'a
  fix b :: "'b option"
  show "LOut (option_l l) (LIn2 (option_l l) a b) = Some a"
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
  show "LOut (prio_l n f l) (LIn1 (prio_l n f l) a) = Some a"
    using lifting_valid_unfold1[OF H] by(auto simp add:prio_l_def)
next
  fix a :: 'a
  fix b :: "'b md_prio"
  show "LOut (prio_l n f l) (LIn2 (prio_l n f l) a b) = Some a"
    using lifting_valid_unfold2[OF H] by(auto simp add:prio_l_def split:md_prio.splits)
qed

lemma fst_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (fst_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (fst_l l) (LIn1 (fst_l l) a) = Some a"
    using lifting_valid_unfold1[OF H] by(auto simp add:fst_l_def)
next
  fix a :: 'a
  fix b :: "('b * 'c)"
  show "LOut (fst_l l) (LIn2 (fst_l l) a b) = Some a"
    using lifting_valid_unfold2[OF H] by(auto simp add:fst_l_def split:prod.splits)
qed

lemma snd_l_valid :
  assumes H : "lifting_valid l"
  shows "lifting_valid (snd_l l)"
proof(rule lifting_valid_intro)
  fix a :: 'a
  show "LOut (snd_l l) (LIn1 (snd_l l) a) = Some a"
    using lifting_valid_unfold1[OF H] by(auto simp add:snd_l_def)
next
  fix a :: 'a
  fix b :: "('c * 'b)"
  show "LOut (snd_l l) (LIn2 (snd_l l) a b) = Some a"
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
  show "LOut (prod_l l1 l2) (LIn1 (prod_l l1 l2) a) = Some a"
    using lifting_valid_unfold1[OF H1, of "fst a"] lifting_valid_unfold1[OF H2, of "snd a"]
    by(auto simp add:prod_l_def split:prod.splits)
next
  fix a :: "'a1 * 'a2"
  fix b :: "'b1 * 'b2"
  show "LOut (prod_l l1 l2) (LIn2 (prod_l l1 l2) a b) = Some a"
    using lifting_valid_unfold2[OF H1] lifting_valid_unfold2[OF H2]
    by(auto simp add:prod_l_def split:prod.splits)
qed
end