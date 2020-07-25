theory LiftInstancesProfunctor imports LiftUtilsProfunctor
begin

(* need some tools for reasoning about sytnax transformations
   along with this we are also going to need proofs that this syn_l
   preserves required properties (possibly just sup_l, but maybe also least
   upper bounds unless we can come up with sufficiently general proofs on a
   per-datatype basis *)

definition syn_l ::
  "('sc \<Rightarrow> 'sb) \<Rightarrow>
   ('sa, 'sb, 'a, 'b) lifting \<Rightarrow>
   ('sa, 'sc, 'a, 'b) lifting" where
"syn_l f t =
  \<lparr> LSyn = (\<lambda> sc . (LSyn t (f sc)))
  , LIn1 = LIn1 t
  , LIn2 = (\<lambda> sa sc a b . LIn2 t sa (f sc) a b)
  , LOut1 = (\<lambda> sc b . LOut1 t (f sc) b) \<rparr>"

(*
identity lifting
*)


definition id_l ::
  "('sb \<Rightarrow> 'sa) \<Rightarrow> ('sa, 'sb, 'a, 'a) lifting" where
"id_l f =
  \<lparr> LSyn = f
  , LIn1 = (\<lambda> sa a . a)
  , LIn2 = (\<lambda> sa1 sa2 a b . a)
  , LOut1 = (\<lambda> sa b . b)\<rparr>" 

lemma id_l_valid : "lifting_valid (id_l f)"
  apply (rule lifting_valid_intro)
     apply(simp add:id_l_def)
    apply(simp add:id_l_def)
  done

definition idl :: "('sa, 'sa, 'a, 'a) lifting" where
"idl = id_l id"

(*
trivial ordering
*)

definition triv_l ::
  "('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa, 'sb, 'a, 'b md_triv) lifting" where
"triv_l t =
  \<lparr> LSyn = LSyn t
  , LIn1 = (\<lambda> sa a . mdt ( LIn1 t sa a))
  , LIn2 = (\<lambda> sa sb a b . (case b of (mdt b') \<Rightarrow> (mdt ( (LIn2 t sa sb a b')))))
  , LOut1 = (\<lambda> sb b . (case b of (mdt b') \<Rightarrow> (LOut1 t sb b')))\<rparr>"

definition triv_l' ::
  "('a, 'b) lifting' \<Rightarrow> ('a, 'b md_triv) lifting'" where
"triv_l' t' =
  (case_md_triv t')"

lemma triv_l_valid :
  fixes l :: "('sa, 'sb, 'a, 'b) lifting"
  assumes H : "lifting_valid l"
  shows "lifting_valid (triv_l l)"
proof(rule lifting_valid_intro)
  fix s :: 'sb
  fix a :: 'a
  show "LOut1 (triv_l l) s (LIn1 (triv_l l) (LSyn (triv_l l) s) a) = a" using lifting_valid_unfold1[OF H]
    by(auto simp add:triv_l_def)
next
  fix s :: 'sb
  fix a :: 'a
  fix b :: "'b md_triv"
  show "LOut1 (triv_l l) s (LIn2 (triv_l l) (LSyn (triv_l l) s) s a b) = a"
    using lifting_valid_unfold2[OF H]
    by(auto simp add:triv_l_def split:md_triv.splits)
qed

(*
option ordering
*)

definition option_l ::
  "('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa, 'sb, 'a, 'b option) lifting" where
"option_l t =
  \<lparr> LSyn = LSyn t
  , LIn1 = (\<lambda> s a . Some ( LIn1 t s a))
  , LIn2 = (\<lambda> sa sb a b . (case b of None \<Rightarrow> Some (LIn1 t sa a)
                                   | Some b' \<Rightarrow> (Some ( (LIn2 t sa sb a b')))))
  , LOut1 = (\<lambda> s b . (case b of Some b' \<Rightarrow> LOut1 t s b'))\<rparr>"

definition option_l' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a, 'b option) lifting'" where
"option_l' t =
  case_option undefined t "

lemma option_l_valid :
  fixes l :: "('sa, 'sb, 'a, 'b) lifting"
  assumes H : "lifting_valid l"
  shows "lifting_valid (option_l l)"
proof(rule lifting_valid_intro)
  fix s :: 'sb
  fix a :: 'a
  show "LOut1 (option_l l) s (LIn1 (option_l l) (LSyn (option_l l) s) a) = a" using lifting_valid_unfold1[OF H]
    by(auto simp add:option_l_def)
next
  fix s :: 'sb
  fix a :: 'a
  fix b :: "'b option"
  show "LOut1 (option_l l) s (LIn2 (option_l l) (LSyn (option_l l) s) s a b) = a"
    using lifting_valid_unfold2[OF H] lifting_valid_unfold1[OF H]
    by(auto simp add:option_l_def split:option.splits)
qed

(*
priorities
*)

(* note: this only allows syntax dispatching. *)
(* TODO: allow dispatch on sb or just sa? *)
definition prio_l ::
  "('sa \<Rightarrow> nat) \<Rightarrow>
  ('sa \<Rightarrow> 'sb \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
  ('sa, 'sb, 'a, 'b) lifting \<Rightarrow>
  ('sa, 'sb, 'a, 'b md_prio) lifting" where
"prio_l f0 f1 t =
  \<lparr> LSyn = LSyn t
  , LIn1 = (\<lambda> s a . mdp (f0 s) (LIn1 t s a))
  , LIn2 = (\<lambda> sa sb a b . (case b of
                         mdp m b' \<Rightarrow> mdp (f1 sa sb m) (LIn2 t sa sb a b')))
  , LOut1 =
      (\<lambda> sb p . (case p of
                 mdp m b \<Rightarrow> LOut1 t sb b))\<rparr>"

definition prio_l' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a, 'b md_prio) lifting'" where
"prio_l' t =
  (\<lambda> p . (case p of
              mdp m b \<Rightarrow> t b))"

(* enables dispatch only on syntax - this should be mostly sufficient *)
lemma prio_l_valid : 
  fixes l :: "('sa, 'sb, 'a, 'b) lifting"
  assumes H : "lifting_valid l"
  shows "lifting_valid (prio_l f0 f1 l)"
proof(rule lifting_valid_intro)
  fix s :: 'sb
  fix a :: 'a
  show "LOut1 (prio_l f0 f1 l) s (LIn1 (prio_l f0 f1 l) (LSyn (prio_l f0 f1 l) s) a) = a"
    using lifting_valid_unfold1[OF H] by(auto simp add:prio_l_def)
next
  fix s :: 'sb
  fix a :: 'a
  fix b :: "'b md_prio"
  show "LOut1 (prio_l f0 f1 l) s (LIn2 (prio_l f0 f1 l) (LSyn (prio_l f0 f1 l) s) s a b) = a"
    using lifting_valid_unfold2[OF H] by(auto simp add:prio_l_def split:md_prio.splits)
qed


definition prio_l_keep :: "('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa, 'sb, 'a, 'b md_prio) lifting" where
"prio_l_keep =
  prio_l (\<lambda> _ . 0) (\<lambda> _ _ n . n)"

definition prio_l_inc :: "('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa, 'sb, 'a, 'b md_prio) lifting" where
"prio_l_inc =
  prio_l (\<lambda> _ . 0) (\<lambda> _ _ x . 1 + x)"

definition prio_l_const :: "nat \<Rightarrow> ('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa, 'sb, 'a, 'b md_prio) lifting" where
"prio_l_const n =
  prio_l (\<lambda> _ . n) (\<lambda> _ _ _ . n)"

definition prio_l_zero ::
"('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa, 'sb, 'a, 'b md_prio) lifting" where
"prio_l_zero =
  prio_l_const 0"

definition prio_l_one ::
"('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa, 'sb, 'a, 'b md_prio) lifting" where
"prio_l_one =
  prio_l_const 1"


(*
products
*)

definition fst_l ::
  "('sa, 'sb, 'a, 'b1) lifting \<Rightarrow>
   ('sa, 'sb, 'a, 'b1 * ('b2 :: Pordb)) lifting" where
"fst_l t =
  \<lparr> LSyn = LSyn t
  , LIn1 = (\<lambda> s a . (LIn1 t s a, \<bottom>))
  , LIn2 = (\<lambda> sa sb a b . (case b of (b1, b2) \<Rightarrow> (LIn2 t sa sb a b1, \<bottom>)))
  , LOut1 = (\<lambda> s x . (LOut1 t s (fst x))) \<rparr>"

definition fst_l' ::
  "('a, 'b1) lifting' \<Rightarrow>
   ('a, 'b1 * 'b2) lifting'" where
"fst_l' t =
  (\<lambda> x . t (fst x))"


lemma fst_l_valid :
  fixes l :: "('sa, 'sb, 'a, 'b1) lifting"
  assumes H : "lifting_valid l"
  shows "lifting_valid (fst_l l :: ('sa, 'sb, 'a, 'b1 * ('b2 :: Pordb)) lifting)"
proof(rule lifting_valid_intro)
  fix s :: 'sb 
  fix a :: 'a
  show "LOut1 (fst_l l) s (LIn1 (fst_l l) (LSyn (fst_l l) s) a) = a"
    using lifting_valid_unfold1[OF H] 
      by(auto simp add:fst_l_def)
next
  fix s :: 'sb
  fix a :: 'a
  fix b :: "('b1 * 'b2)"
  show "LOut1 (fst_l l) s (LIn2 (fst_l l) (LSyn (fst_l l) s) s a b) = a"
    using lifting_valid_unfold2[OF H] by(auto simp add:fst_l_def split:prod.splits)
qed

definition snd_l ::
  "('sa, 'sb, 'a, 'b2) lifting \<Rightarrow>
   ('sa, 'sb, 'a, ('b1 :: Pordb) * 'b2) lifting" where
"snd_l t =
  \<lparr> LSyn = LSyn t
  , LIn1 = (\<lambda> s a . (\<bottom>, LIn1 t s a))
  , LIn2 = (\<lambda> sa sb a b . (case b of (b1, b2) \<Rightarrow> (\<bottom>, LIn2 t sa sb a b2)))
  , LOut1 = (\<lambda> s x . (LOut1 t s (snd x))) \<rparr>"

definition snd_l' ::
  "('a, 'b2) lifting' \<Rightarrow>
   ('a, 'b1 * 'b2) lifting'" where
"snd_l' t =
  (\<lambda> x . (t (snd x)))"

lemma snd_l_valid :
  fixes l :: "('sa, 'sb, 'a, 'b2) lifting"
  assumes H : "lifting_valid l"
  shows "lifting_valid (snd_l l :: ('sa, 'sb, 'a, ('b1 :: Pordb) * 'b2) lifting)"
proof(rule lifting_valid_intro)
  fix s :: 'sb
  fix a :: 'a
  show " LOut1 (snd_l l) s (LIn1 (snd_l l) (LSyn (snd_l l) s) a) = a"
    using lifting_valid_unfold1[OF H] by(auto simp add:snd_l_def)
next
  fix s :: 'sb
  fix a :: 'a
  fix b :: "('b1 * 'b2)"
  show "LOut1 (snd_l l) s (LIn2 (snd_l l) (LSyn (snd_l l) s) s a b) = a"
    using lifting_valid_unfold2[OF H] by(auto simp add:snd_l_def split:prod.splits)
qed

(* NB: assumes that syntax lifting for t1 and t2 are the same. *)
(*
definition prod_l1 ::
  "('sa, 'sb, 'a1, 'b1) lifting \<Rightarrow>
   ('sa, 'sb, 'a2, 'b2) lifting \<Rightarrow>
   ('sa, 'sb, 'a1 * 'a2, 'b1 * 'b2) lifting" where
"prod_l1 t1 t2 =
  \<lparr> LSyn = (\<lambda> s . (LSyn t1 s))
  , LIn1 =
    (\<lambda> s a . (case a of (a1, a2) \<Rightarrow> (LIn1 t1 s a1, LIn1 t2 s a2)))
  , LIn2 =
    (\<lambda> sa sb a b .
        (case a of (a1, a2) \<Rightarrow>
        (case b of (b1, b2) \<Rightarrow>
            (LIn2 t1 sa sb a1 b1, LIn2 t2 sa sb a2 b2))))
  , LOut1 =
    (\<lambda> s b . (case b of (b1, b2) \<Rightarrow>
                (LOut1 t1 s b1, LOut1 t2 s b2))) \<rparr>"
*)

definition prod_l1 ::
  "('sa, 'sb, 'a1, 'b1) lifting \<Rightarrow>
   ('sa, 'sb, 'a2, 'b2) lifting \<Rightarrow>
   ('sa, 'sb, 'a1 * 'a2, 'b1 * 'b2) lifting" where
"prod_l1 t1 t2 =
  \<lparr> LSyn = (\<lambda> s . if LSyn t1 s = LSyn t2 s then LSyn t1 s else undefined)
  , LIn1 =
    (\<lambda> s a . (case a of (a1, a2) \<Rightarrow> (LIn1 t1 s a1, LIn1 t2 s a2)))
  , LIn2 =
    (\<lambda> sa sb a b .
        (case a of (a1, a2) \<Rightarrow>
        (case b of (b1, b2) \<Rightarrow>
            (LIn2 t1 sa sb a1 b1, LIn2 t2 sa sb a2 b2))))
  , LOut1 =
    (\<lambda> s b . (case b of (b1, b2) \<Rightarrow>
                (LOut1 t1 s b1, LOut1 t2 s b2))) \<rparr>"


definition sync :: "('sa, 'sb, 'a1, 'b1) lifting \<Rightarrow> ('sa, 'sb, 'a2, 'b2) lifting \<Rightarrow> bool" where
"sync t1 t2 = (\<forall> s . LSyn t1 s = LSyn t2 s)"

lemma syncI :
  fixes t1 t2 :: "('sa, 'sb, 'a1, 'b1) lifting"
  fixes s :: "('sb)"
  assumes H : "\<And> s . LSyn l1 s = LSyn l2 s"
  shows "sync l1 l2" using H
  by(auto simp add:sync_def)

lemma syncD :
  fixes t1 t2 :: "('sa, 'sb, 'a1, 'b1) lifting"
  fixes s :: "('sb)"
  assumes H : "sync l1 l2"
  shows "LSyn l1 s = LSyn l2 s" using H
  by(auto simp add:sync_def)

lemma prod_l1_valid :
  fixes l1 :: "('sa, 'sb, 'a1, 'b1) lifting"
  fixes l2 :: "('sa, 'sb, 'a2, 'b2) lifting"
  assumes H1 : "lifting_valid l1"
  assumes H2 : "lifting_valid l2"
  assumes Hsyn : "sync l1 l2"
  shows "lifting_valid (prod_l1 l1 l2)"
proof(rule lifting_valid_intro)
  fix s :: 'sb
  fix a :: "'a1 * 'a2"
  show "LOut1 (prod_l1 l1 l2) s (LIn1 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) a) = a"
    using lifting_valid_unfold1[OF H1, of s "fst a"] lifting_valid_unfold1[OF H2, of s "snd a"]
    syncD[OF Hsyn]
    by(auto simp add:prod_l1_def split:prod.splits)
next
  fix s :: 'sb
  fix a :: "'a1 * 'a2"
  fix b :: "'b1 * 'b2"
  show "LOut1 (prod_l1 l1 l2) s (LIn2 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) s a b) = a"
    using lifting_valid_unfold2[OF H1] lifting_valid_unfold2[OF H2] syncD[OF Hsyn]
    by(auto simp add:prod_l1_def split:prod.splits)
qed

definition syn_prod :: "('x \<Rightarrow> 'x1) \<Rightarrow> ('x \<Rightarrow> 'x2) \<Rightarrow> ('x \<Rightarrow> ('x1 * 'x2))"
  where
"syn_prod f1 f2 x = (f1 x, f2 x)"



lemma sup_l1_prod_fst :
  fixes l1  :: "('sa, 'sb, 'a1, 'b1 :: Mergeableb) lifting"
  fixes l1' :: "('sap, 'sb, 'a1p, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('sa, 'sb, 'a2, 'b2 :: Mergeableb) lifting"
  assumes Hsyn : "sync l1 l2"
  assumes H : "sup_l l1 l1'"
  shows "sup_l (prod_l1 l1 l2) (fst_l l1')"
proof(rule sup_l_intro)
  fix s :: "'sb"
  fix a1 :: "('a1 \<times> 'a2)" 
  fix a1p :: "'a1p"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub where Hub : "is_sup {LIn1 l1 (LSyn l1 s) x1, LIn1 l1' (LSyn l1' s) a1p} ub"
      using sup_l_unfold1[OF H, of s x1] Hx
      by(auto simp add:prod_l1_def fst_l_def has_sup_def split:prod.splits)
  
    have "is_sup {LIn1 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) a1, LIn1 (fst_l l1') (LSyn (fst_l l1') s) a1p} (ub, LIn1 l2 (LSyn l2 s) x2)" using  Hub Hx
      syncD[OF Hsyn]
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l1_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) a1, LIn1 (fst_l l1') (LSyn (fst_l l1') s) a1p}" by (auto simp add:has_sup_def)
next
  fix s :: "'sb"
  fix a1::"'a1 \<times> 'a2"
  fix a1p::"'a1p"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub1 : "has_sup {y1, z1}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l1 (LSyn l1 s) s x1 y1, LIn2 l1' (LSyn l1' s) s a1p z1} ub"
      using sup_l_unfold2[OF H Hub1, of s x1] Hx Hy Hz
      by(auto simp add:prod_l1_def fst_l_def has_sup_def split:prod.splits)

    have "is_sup {LIn2 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) s a1 b1, 
                  LIn2 (fst_l l1') (LSyn (fst_l l1') s)   s a1p b2} (ub, LIn2 l2 (LSyn l2 s) s x2 y2)" using  Hub Hx Hy Hz
      syncD[OF Hsyn]
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l1_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) s a1 b1, LIn2 (fst_l l1') (LSyn (fst_l l1') s) s a1p b2}" by (auto simp add:has_sup_def)
qed

lemma sup_l1_prod_snd :
  fixes l1  :: "('sa, 'sb, 'a1, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('sa, 'sb, 'a2, 'b2 :: Mergeableb) lifting"
  fixes l2' :: "('sap, 'sb, 'a2p, 'b2 :: Mergeableb) lifting"
  assumes Hsync : "sync l1 l2"
  assumes H : "sup_l l2 l2'"
  shows "sup_l (prod_l1 l1 l2) (snd_l l2')"
proof(rule sup_l_intro)
  fix s :: "'sb"
  fix a1 :: "('a1 \<times> 'a2)" 
  fix a2 :: "'a2p"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub :: 'b2 where Hub : "is_sup {LIn1 l2 (LSyn l2 s) x2, LIn1 l2' (LSyn l2' s) a2} ub"
      using sup_l_unfold1[OF H, of s x2] Hx
      by(auto simp add:prod_l1_def has_sup_def split:prod.splits)
  
    have "is_sup {LIn1 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) a1, LIn1 (snd_l l2') (LSyn (snd_l l2') s) a2} (LIn1 l1 (LSyn l1 s) x1, ub)" using  Hub Hx
      syncD[OF Hsync]
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l1_def snd_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) a1, LIn1 (snd_l l2') (LSyn (snd_l l2') s) a2}" by (auto simp add:has_sup_def)
next
  fix s :: "'sb"
  fix a1::"'a1 \<times> 'a2"
  fix a2::"'a2p"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub2 : "has_sup {y2, z2}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l2 (LSyn l2 s) s x2 y2, LIn2 l2' (LSyn l2' s) s a2 z2} ub"
      using sup_l_unfold2[OF H Hub2, of s x2] Hx Hy Hz 
      by(auto simp add:prod_l1_def fst_l_def has_sup_def split:prod.splits)

    have "is_sup {LIn2 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) s a1 b1, 
                  LIn2 (snd_l l2') (LSyn (snd_l l2') s) s a2 b2} (LIn2 l1 (LSyn l1 s) s x1 y1, ub)" using  Hub Hx Hy Hz
      syncD[OF Hsync]
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l1_def snd_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l1 l1 l2) (LSyn (prod_l1 l1 l2) s) s a1 b1,
                 LIn2 (snd_l l2') (LSyn (snd_l l2') s) s a2 b2}" by (auto simp add:has_sup_def)
qed


definition prod_l ::
  "('sa1, 'sb, 'a1, 'b1) lifting \<Rightarrow>
   ('sa2, 'sb, 'a2, 'b2) lifting \<Rightarrow>
   ('sa1 * 'sa2, 'sb, 'a1 * 'a2, 'b1 * 'b2) lifting" where
"prod_l t1 t2 =
  \<lparr> LSyn = (\<lambda> s . (LSyn t1 s, LSyn t2 s))
  , LIn1 =
    (\<lambda> s a . (case s of (s1, s2) \<Rightarrow>
             (case a of (a1, a2) \<Rightarrow> (LIn1 t1 s1 a1, LIn1 t2 s2 a2))))
  , LIn2 =
    (\<lambda> sa12 sb a b .
        (case sa12 of (sa1, sa2) \<Rightarrow>
        (case a of (a1, a2) \<Rightarrow>
        (case b of (b1, b2) \<Rightarrow>
            (LIn2 t1 sa1 sb a1 b1, LIn2 t2 sa2 sb a2 b2)))))
  , LOut1 =
    (\<lambda> s b . (case b of (b1, b2) \<Rightarrow>
                (LOut1 t1 s b1, LOut1 t2 s b2))) \<rparr>"
                  
definition prod_l' ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a2, 'b2) lifting' \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2) lifting'" where
"prod_l' t1 t2 =
  (\<lambda> x . (case x of (x1, x2) \<Rightarrow> (t1 x1, t2 x2)))"

lemma prod_l_valid :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b1) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b2) lifting"
  assumes H1 : "lifting_valid l1"
  assumes H2 : "lifting_valid l2"
  shows "lifting_valid (prod_l l1 l2)"
proof(rule lifting_valid_intro)
  fix s :: 'sb
  fix a :: "'a1 * 'a2"
  show "LOut1 (prod_l l1 l2) s (LIn1 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) a) = a"
    using lifting_valid_unfold1[OF H1, of s "fst a"] lifting_valid_unfold1[OF H2, of s "snd a"]
    by(auto simp add:prod_l_def split:prod.splits)
next
  fix s :: 'sb
  fix a :: "'a1 * 'a2"
  fix b :: "'b1 * 'b2"
  show "LOut1 (prod_l l1 l2) s (LIn2 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) s a b) = a"
    using lifting_valid_unfold2[OF H1] lifting_valid_unfold2[OF H2]
    by(auto simp add:prod_l_def split:prod.splits)
qed

declare [[show_types]]

lemma sup_l_prod_fst :
  fixes l1  :: "('sa1, 'sb, 'a1, 'b1 :: Mergeableb) lifting"
  fixes l1' :: "('sa1p, 'sb, 'a1p, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('sa2, 'sb, 'a2, 'b2 :: Mergeableb) lifting"
  assumes H : "sup_l l1 l1'"
  shows "sup_l (prod_l l1 l2) (fst_l l1')"
proof(rule sup_l_intro)
  fix s :: "'sb"
  fix a1 :: "('a1 \<times> 'a2)" 
  fix a1p :: "'a1p"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub where Hub : "is_sup {LIn1 l1 (LSyn l1 s) x1, LIn1 l1' (LSyn l1' s) a1p} ub"
      using sup_l_unfold1[OF H, of s x1] Hx
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) a1, LIn1 (fst_l l1') (LSyn (fst_l l1') s) a1p} (ub, LIn1 l2 (LSyn l2 s) x2)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) a1, LIn1 (fst_l l1') (LSyn (fst_l l1') s) a1p}" by (auto simp add:has_sup_def)
next
  fix s :: "'sb"
  fix a1::"'a1 \<times> 'a2"
  fix a1p::"'a1p"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub1 : "has_sup {y1, z1}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l1 (LSyn l1 s) s x1 y1, LIn2 l1' (LSyn l1' s) s a1p z1} ub"
      using sup_l_unfold2[OF H Hub1, of s x1] Hx Hy Hz
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)

    have "is_sup {LIn2 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) s a1 b1, 
                  LIn2 (fst_l l1') (LSyn (fst_l l1') s)   s a1p b2} (ub, LIn2 l2 (LSyn l2 s) s x2 y2)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def fst_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) s a1 b1, LIn2 (fst_l l1') (LSyn (fst_l l1') s) s a1p b2}" by (auto simp add:has_sup_def)
qed

lemma sup_lg_prod_snd :
  fixes l1  :: "('sa1, 'sb, 'a1, 'b1 :: Mergeableb) lifting"
  fixes l2  :: "('sa2, 'sb, 'a2, 'b2 :: Mergeableb) lifting"
  fixes l2' :: "('sa2p, 'sb, 'a2p, 'b2 :: Mergeableb) lifting"
  assumes H : "sup_l l2 l2'"
  shows "sup_l (prod_l l1 l2) (snd_l l2')"
proof(rule sup_l_intro)
  fix s :: "'sb"
  fix a1 :: "('a1 \<times> 'a2)" 
  fix a2 :: "'a2p"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub :: 'b2 where Hub : "is_sup {LIn1 l2 (LSyn l2 s) x2, LIn1 l2' (LSyn l2' s) a2} ub"
      using sup_l_unfold1[OF H, of s x2] Hx
      by(auto simp add:prod_l_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) a1, LIn1 (snd_l l2') (LSyn (snd_l l2') s) a2} (LIn1 l1 (LSyn l1 s) x1, ub)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def snd_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) a1, LIn1 (snd_l l2') (LSyn (snd_l l2') s) a2}" by (auto simp add:has_sup_def)
next
  fix s :: "'sb"
  fix a1::"'a1 \<times> 'a2"
  fix a2::"'a2p"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub2 : "has_sup {y2, z2}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2 l2 (LSyn l2 s) s x2 y2, LIn2 l2' (LSyn l2' s) s a2 z2} ub"
      using sup_l_unfold2[OF H Hub2, of s x2] Hx Hy Hz
      by(auto simp add:prod_l_def fst_l_def has_sup_def split:prod.splits)

    have "is_sup {LIn2 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) s a1 b1, 
                  LIn2 (snd_l l2') (LSyn (snd_l l2') s) s a2 b2} (LIn2 l1 (LSyn l1 s) s x1 y1, ub)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_l_def snd_l_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2 (prod_l l1 l2) (LSyn (prod_l l1 l2) s) s a1 b1,
                 LIn2 (snd_l l2') (LSyn (snd_l l2') s) s a2 b2}" by (auto simp add:has_sup_def)
qed

lemma prio_sup :
  fixes b1 b2 :: "('b :: Pordb) md_prio"
  shows "has_sup {b1, b2}"
proof-
  obtain b1p and b1' where Hb1 : "b1 = mdp b1p b1'" by(cases b1; auto)
  obtain b2p and b2' where Hb2 : "b2 = mdp b2p b2'" by (cases b2; auto)

  have "is_ub {b1, b2} (mdp ((max b1p b2p) + 1) \<bottom>)"
    using Hb1 Hb2
    by(auto simp  add: is_ub_def prio_pleq prio_bot)

  hence "has_ub {b1, b2}" by (auto simp add:has_ub_def)

  thus "has_sup {b1, b2}" by(rule complete2; auto)
qed

lemma sup_l_prio :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b :: Pordb) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b :: Pordb) lifting"
  shows "sup_l (prio_l f0_1 f1_1 l1) (prio_l f0_2 f1_2 l2)"
proof(rule sup_l_intro)
  fix s :: "'sb"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  show "has_sup {LIn1 (prio_l f0_1 f1_1 l1) (LSyn (prio_l f0_1 f1_1 l1) s) a1, LIn1 (prio_l f0_2 f1_2 l2) (LSyn (prio_l f0_2 f1_2 l2) s) a2}"
    by(rule prio_sup)
next
  fix s :: "'sb"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b1 b2 :: "'b md_prio"
  assume H : "has_sup {b1, b2}"
  show "has_sup
        {LIn2 (prio_l f0_1 f1_1 l1) (LSyn (prio_l f0_1 f1_1 l1) s) s a1 b1, LIn2 (prio_l f0_2 f1_2 l2) (LSyn (prio_l f0_2 f1_2 l2) s) s a2 b2}"
    by(rule prio_sup)
qed

(* prios = sort of different
   we probably need to relate the details of the functions?
   (or do we not? md_prio always has an upper bound *)
lemma sup_l_inc_zero :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b :: Mergeableb) lifting"
  fixes l2:: "('sa2, 'sb, 'a2, 'b :: Mergeableb) lifting"
  shows "sup_l (prio_l_zero l1) (prio_l_inc l2)"
  unfolding prio_l_zero_def prio_l_inc_def prio_l_const_def by(rule sup_l_prio)


(*
variable maps
*)

(* simplest case for lifting into variable map. only allows 
   dispatch based on syntax. (further, only "inner" ('sa) syntax) *)
definition oalist_l ::
   "('sa \<Rightarrow> 'k :: linorder) \<Rightarrow>
    ('sa, 'sb, 'a, 'b) lifting \<Rightarrow>
    ('sa, 'sb, 'a, ('k, 'b) oalist) lifting" where
"oalist_l f t =
  \<lparr> LSyn = LSyn t
  , LIn1 = (\<lambda> s a . (let k = f s in
                     (update k (LIn1 t s a) empty)))
  , LIn2 = (\<lambda> sa sb a l .
            (let k = f sa in
              (case get l k of
                None \<Rightarrow> (update k (LIn1 t sa a) l)
                | Some v \<Rightarrow> (update k (LIn2 t sa sb a v) l))))
  , LOut1 = (\<lambda> s l . (case get l (f (LSyn t s)) of Some a \<Rightarrow> LOut1 t s a))\<rparr>"

lemma oalist_l_valid :
  fixes f :: "('sa \<Rightarrow> 'k :: linorder)"
  fixes lv :: "('sa, 'sb, 'a, 'b) lifting"
  assumes Hv : "lifting_valid lv"
  shows "lifting_valid (oalist_l f lv)"
proof(rule lifting_valid_intro)
  fix s :: 'sb
  fix a :: 'a
  show " LOut1 (oalist_l f lv) s (LIn1 (oalist_l f lv) (LSyn (oalist_l f lv) s) a) = a" using lifting_valid_unfold1[OF Hv]
    by(auto simp add:oalist_l_def Let_def get_update split:prod.splits option.splits)
next
  fix s :: 'sb
  fix a :: 'a
  fix b :: "('k, 'b) oalist"
  show "LOut1 (oalist_l f lv) s (LIn2 (oalist_l f lv) (LSyn (oalist_l f lv) s) s a b) = a" using 
        lifting_valid_unfold1[OF Hv]
        lifting_valid_unfold2[OF Hv]
    by(auto simp add:oalist_l_def Let_def get_update split:prod.splits option.splits)
qed


(* allows more interesting dispatch (based on state), but
   at the cost of storing the key, which means we cannot
   merge semantics that update keys in a different order *)
(*
definition oalist_k_l ::
  "('x, 'a, 'k :: linorder) lifting \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow>
   ('x, 'a, ('k * ('k, 'b) oalist)) lifting" where
"oalist_k_l tk tv =
  \<lparr> LIn1 = (\<lambda> s a . (let k = LIn1 tk s a in
                     (k, update k (LIn1 tv s a) empty)))
  , LIn2 = (\<lambda> s a k'l .
            (case k'l of
              (k', l) \<Rightarrow>
                (let k = LIn2 tk s a k' in
                (case get l k of
                  None \<Rightarrow> (k, update k (LIn1 tv s a) l)
                  | Some v \<Rightarrow> (k, update k (LIn2 tv s a v) l)))))
  , LOut1 = (\<lambda> s kl .
              (case kl of
                (k, l) \<Rightarrow> (case get l k of Some a \<Rightarrow> LOut1 tv s a)))\<rparr>"
*)

(*
lemma oalist_k_l_valid :
  fixes lk :: "('x, 'a, 'k :: linorder) lifting"
  fixes lv :: "('x, 'a, 'b) lifting"
  assumes Hk : "lifting_valid lk"
  assumes Hv : "lifting_valid lv"
  shows "lifting_valid (oalist_k_l lk lv)"
proof(rule lifting_valid_intro)
  fix s :: 'x
  fix a :: 'a
  show "LOut1 (oalist_k_l lk lv) s (LIn1 (oalist_k_l lk lv) s a) = a" using lifting_valid_unfold1[OF Hv]
    by(auto simp add:oalist_k_l_def Let_def get_update split:prod.splits option.splits)
next
  fix s :: 'x
  fix a :: 'a
  fix b :: "'k * ('k, 'b) oalist"
  show "LOut1 (oalist_k_l lk lv) s (LIn2 (oalist_k_l lk lv) s a b) = a" using 
        lifting_valid_unfold1[OF Hv]
        lifting_valid_unfold2[OF Hv]
    by(auto simp add:oalist_k_l_def Let_def get_update split:prod.splits option.splits)
qed
*)

(* finally, here we allow keymaps, which might enable more interesting merges
   however we will need to reset the kmap in between commands. *)
(* should double check this *)
(*
definition oalist_kmap_l ::
  "('x, 'a, 'k :: linorder) lifting \<Rightarrow>
   ('x, 'a, 'b) lifting \<Rightarrow>
   ('x, 'a, ('k kmap * ('k, 'b) oalist)) lifting" where
"oalist_kmap_l tk tv =
  \<lparr> LIn1 = (\<lambda> s a . (let k = LIn1 tk s a in
                     (to_oalist [(k, ())], update k (LIn1 tv s a) empty)))
  , LIn2 = (\<lambda> s a k'l .
            (case k'l of
              (k', l) \<Rightarrow>
                (let k = kmap_singleton k' in
                (case get l k of
                  None \<Rightarrow> (k' , update k (LIn1 tv s a) l)
                  | Some v \<Rightarrow> (k', update k (LIn2 tv s a v) l)))))
  , LOut1 = (\<lambda> s kl .
              (case kl of
                (km, l) \<Rightarrow> (case get l (kmap_singleton km) of Some a \<Rightarrow> LOut1 tv s a)))\<rparr>"
*)

(* another approach would be to return sets. this might we worth exploring later. *)

end