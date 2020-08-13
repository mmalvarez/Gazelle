theory LiftUtils imports  "../MergeableTc/MergeableInstances" "../MergeableTc/MergeableAList"

begin


(* lifting' is used for syntax *)
type_synonym ('a, 'b) lifting' = "('b \<Rightarrow> 'a)"

(* key abstraction used to lift semantics into larger types *)
record ('syn, 'a, 'b) lifting =
  LIn1 :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b)"
  LIn2 :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)"
  LOut1 :: "('syn \<Rightarrow> 'b \<Rightarrow> 'a)"

definition l_adapt ::
  "('syn1 \<Rightarrow> 'syn2) \<Rightarrow>
   ('syn2, 'a, 'b) lifting \<Rightarrow>
   ('syn1, 'a, 'b) lifting" where
"l_adapt f t =
  \<lparr> LIn1 = (\<lambda> s a . LIn1 t (f s) a)
  , LIn2 = (\<lambda> s a b . LIn2 t (f s) a b)
  , LOut1 = (\<lambda> s b . LOut1 t (f s) b) \<rparr>"

definition l_map ::
  "('x, 'a, 'b) lifting \<Rightarrow>
    ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"l_map l sem syn st =
  (LIn2 l syn (sem syn (LOut1 l syn st)) st)"

definition l_map2' ::
    "('a1, 'b1) lifting' \<Rightarrow>
     ('a1, 'a2, 'b2) lifting \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"l_map2' l' l sem syn st =
  (LIn2 l (l' syn) (sem (l' syn) (LOut1 l (l' syn) st)) st)"


definition l_pred :: "('x, 'a, 'b) lifting \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred t P =
  (\<lambda> s b . P s (LOut1 t s b))"

definition l_pred' :: "('a, 'b) lifting' \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where
"l_pred' t P =
  (\<lambda> b . P (t b))"


(* we also want 2 notions of lifting preds over functions
   (1 for semantics only; 1 for syntax) *)

(* LOut2 or LOut1 for the second one?  *)
definition l_pred_step ::
  "('x, 'a, 'b) lifting \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('x \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step l P s st1 st2 =
        (P s (LOut1 l s st1) (LOut1 l s st2))"

definition l_pred_step' ::
  "('a, 'b) lifting' \<Rightarrow>
   ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step' l P st1 st2 =
        (P (l st1) (l st2))"

definition l_pred_step2' ::
  "('s1, 's2) lifting' \<Rightarrow>
   ('s1, 'b1, 'b2) lifting \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool) \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step2' l1 l2 P syn st1 st2 =
   (P (l1 syn) (LOut1 l2 (l1 syn) st1) (LOut1 l2 (l1 syn) st2))"

definition l_val ::
  "('x, 'a, 'b) lifting \<Rightarrow>
   'x \<Rightarrow> 'a \<Rightarrow> 'b" where
"l_val l s a = LIn1 l s a"

definition lifting_valid ::
  "('x, 'a, 'b) lifting \<Rightarrow> bool" where
"lifting_valid l =
 ((\<forall> s a .  LOut1 l s (LIn1 l s a) = a) \<and>
  (\<forall> s a b . LOut1 l s (LIn2 l s a b) = a))"

lemma lifting_valid_intro :
  assumes H1 : "\<And> s a .  LOut1 l s (LIn1 l s a) = a"
  assumes H2 : "\<And> s a b . LOut1 l s (LIn2 l s a b) = a"
  shows "lifting_valid l"
  using H1 H2
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_unfold1 :
  assumes H : "lifting_valid l"
  shows "LOut1 l s (LIn1 l s a) = a"
  using H by (auto simp add:lifting_valid_def)

lemma lifting_valid_unfold2 :
  assumes H : "lifting_valid l"
  shows "LOut1 l s (LIn2 l s a b) = a"
  using H by (auto simp add:lifting_valid_def)


lemma l_adapt_valid :
  fixes f :: "('x1 \<Rightarrow> 'x2)"  
  fixes t :: "('x2, 'a, 'b) lifting"
  assumes H : "lifting_valid t"
  shows "lifting_valid (l_adapt f t)" using H
  by(auto simp add:lifting_valid_def l_adapt_def)

lemma pred_lift2' :
  assumes Hv : "lifting_valid l2"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut1 l2 x1 x2' = x2"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step2' l1 l2 P (x1') (x2') (l_map2' l1 l2 f (x1') (x2'))"
  using Hsyn Hsem HP lifting_valid_unfold2[OF Hv] 
  by(cases l2; auto simp add:l_pred_step2'_def l_map2'_def)




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



(* same syntax ("pointwise")? or all syntaxes? *)
definition sup_l ::
  "('x \<Rightarrow> 'x1) \<Rightarrow>
   ('x \<Rightarrow> 'x2) \<Rightarrow>
   ('x1, 'a1, ('b :: Pord)) lifting \<Rightarrow>
   ('x2, 'a2, ('b :: Pord)) lifting \<Rightarrow>
   bool" where
"sup_l ls1 ls2 l1 l2 =
  (\<forall> s a1 a2 b1 b2 .
    has_sup {LIn1 l1 (ls1 s) a1, LIn1 l2 (ls2 s) a2} \<and>
    (has_sup {b1, b2} \<longrightarrow> has_sup {LIn2 l1 (ls1 s) a1 b1, LIn2 l2 (ls2 s) a2 b2}))"

lemma sup_l_intro :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord) lifting"
  fixes l2 :: "('x2, 'a2, 'b :: Pord) lifting"
  assumes H1 : "\<And> s a1 a2 . has_sup {LIn1 l1 (ls1 s) a1, LIn1 l2 (ls2 s) a2}"
  assumes H2 : "\<And> s a1 a2 b1 b2 . has_sup {b1, b2} \<Longrightarrow> has_sup {LIn2 l1 (ls1 s) a1 b1, LIn2 l2 (ls2 s) a2 b2}"
  shows "sup_l ls1 ls2 l1 l2" using H1 H2
  by(auto simp add:sup_l_def)

lemma sup_l_unfold1 :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord) lifting"
  fixes l2 :: "('x2, 'a2, 'b :: Pord) lifting"
  assumes H : "sup_l ls1 ls2 l1 l2"  
  shows "has_sup {LIn1 l1 (ls1 s) a1, LIn1 l2 (ls2 s) a2}"
  using H   by(auto simp add:sup_l_def)

lemma sup_l_unfold2 :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord) lifting"
  fixes l2 :: "('x2, 'a2, 'b :: Pord) lifting"
  assumes Hs : "sup_l ls1 ls2 l1 l2"
  assumes Hb : "has_sup {b1, b2}"
  shows "has_sup {LIn2 l1 (ls1 s) a1 b1, LIn2 l2 (ls2 s) a2 b2}"
  using  Hb Hs
  by(auto simp add:sup_l_def)

(*
lemma sup_lg_prod_fst :
  fixes l1  :: "('x, 'a1, 'b1 :: Mergeableb) lifting_gen"
  fixes l1' :: "('x, 'a2, 'b1 :: Mergeableb) lifting_gen"
  fixes l2  :: "('x, 'a3, 'b2 :: Mergeableb) lifting_gen"
  assumes H : "sup_lg l1 l1'"
  shows "sup_lg (prod_lg l1 l2) (fst_lg l1')"
proof(rule sup_lg_intro)
  fix s :: "'x"
  fix a1 :: "('a1 \<times> 'a3)" 
  fix a2 :: "'a2"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub where Hub : "is_sup {LIn1_g l1 s x1, LIn1_g l1' s a2} ub"
      using sup_lg_unfold1[OF H, of s x1] Hx
      by(auto simp add:prod_lg_def fst_lg_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1_g (prod_lg l1 l2) s a1, LIn1_g (fst_lg l1') s a2} (ub, LIn1_g l2 s x2)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_lg_def fst_lg_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1_g (prod_lg l1 l2) s a1, LIn1_g (fst_lg l1') s a2}" by (auto simp add:has_sup_def)
next
  fix s :: "'x"
  fix a1::"'a1 \<times> 'a3"
  fix a2::"'a2"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub1 : "has_sup {y1, z1}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2_g l1 s x1 y1, LIn2_g l1' s a2 z1} ub"
      using sup_lg_unfold2[OF H Hub1, of s x1] Hx Hy Hz
      by(auto simp add:prod_lg_def fst_lg_def has_sup_def split:prod.splits)

  have "is_sup {LIn2_g (prod_lg l1 l2) s a1 b1, LIn2_g (fst_lg l1') s a2 b2} (ub, LIn2_g l2 s x2 y2)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_lg_def fst_lg_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2_g (prod_lg l1 l2) s a1 b1, LIn2_g (fst_lg l1') s a2 b2}" by (auto simp add:has_sup_def)
qed

lemma sup_lg_prod_snd :
  fixes l1  :: "('x, 'a1, 'b1 :: Mergeableb) lifting_gen"
  fixes l2  :: "('x, 'a2, 'b2 :: Mergeableb) lifting_gen"
  fixes l2' :: "('x, 'a3, 'b2 :: Mergeableb) lifting_gen"
  assumes H : "sup_lg l2 l2'"
  shows "sup_lg (prod_lg l1 l2) (snd_lg l2')"
proof(rule sup_lg_intro)
  fix s :: "'x"
  fix a1 :: "('a1 \<times> 'a2)" 
  fix a2 :: "'a3"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain ub :: 'b2 where Hub : "is_sup {LIn1_g l2 s x2, LIn1_g l2' s a2} ub"
      using sup_lg_unfold1[OF H, of s x2] Hx
      by(auto simp add:prod_lg_def fst_lg_def has_sup_def split:prod.splits)
  
  have "is_sup {LIn1_g (prod_lg l1 l2) s a1, LIn1_g (snd_lg l2') s a2} (LIn1_g l1 s x1, ub)" using  Hub Hx
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_lg_def snd_lg_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn1_g (prod_lg l1 l2) s a1, LIn1_g (snd_lg l2') s a2}" by (auto simp add:has_sup_def)
next
  fix s :: "'x"
  fix a1::"'a1 \<times> 'a2"
  fix a2::"'a3"
  fix b1 b2:: "'b1 \<times> 'b2"
  assume Hb : "has_sup {b1, b2}"
  obtain x1 and x2 where Hx : "a1 = (x1, x2)" by (cases a1; auto)
  obtain y1 and y2 where Hy : "b1 = (y1, y2)" by (cases b1; auto)
  obtain z1 and z2 where Hz : "b2 = (z1, z2)" by (cases b2; auto)

  have Hub2 : "has_sup {y2, z2}" using Hy Hz Hb
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def prod_pleq)

  obtain ub where Hub : "is_sup {LIn2_g l2 s x2 y2, LIn2_g l2' s a2 z2} ub"
      using sup_lg_unfold2[OF H Hub2, of s x2] Hx Hy Hz
      by(auto simp add:prod_lg_def fst_lg_def has_sup_def split:prod.splits)

  have "is_sup {LIn2_g (prod_lg l1 l2) s a1 b1, LIn2_g (snd_lg l2') s a2 b2} (LIn2_g l1 s x1 y1, ub)" using  Hub Hx Hy Hz
    by(auto simp add:has_sup_def is_sup_def is_least_def is_ub_def
        prod_pleq prod_lg_def snd_lg_def bot_spec leq_refl split:prod.splits)
  thus "has_sup {LIn2_g (prod_lg l1 l2) s a1 b1, LIn2_g (snd_lg l2') s a2 b2}" by (auto simp add:has_sup_def)
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

lemma sup_lg_prio :
  fixes l1 :: "('x, 'a1, 'b :: Pordb) lifting_gen"
  fixes l2 :: "('x, 'a2, 'b :: Pordb) lifting_gen"
  shows "sup_lg (prio_lg f0_1 f1_1 l1) (prio_lg f0_2 f1_2 l2)"
proof(rule sup_lg_intro)
  fix s :: "'x"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  show "has_sup {LIn1_g (prio_lg f0_1 f1_1 l1) s a1, LIn1_g (prio_lg f0_2 f1_2 l2) s a2}"
    by(rule prio_sup)
next
  fix s :: "'x"
  fix a1 :: "'a1"
  fix a2 :: "'a2"
  fix b1 b2 :: "'b md_prio"
  assume H : "has_sup {b1, b2}"
  show "has_sup {LIn2_g (prio_lg f0_1 f1_1 l1) s a1 b1, LIn2_g (prio_lg f0_2 f1_2 l2) s a2 b2}"
    by(rule prio_sup)
qed

(* prios = sort of different
   we probably need to relate the details of the functions?
   (or do we not? md_prio always has an upper bound *)
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
*)

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
term "l_map2'"

(* TODO: "dimap"/profunctor
   make the mapping of syntax explicit here *)
lemma sup_l_pres :
  fixes ls1 :: "'syn \<Rightarrow> 'syn1"
  fixes ls2 :: "'syn \<Rightarrow> 'syn2"
  fixes l1 :: "('syn1, 'a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('syn2, 'a2, 'b :: Mergeable) lifting"
  fixes f1 :: "'syn1 \<Rightarrow> 'a1 \<Rightarrow> 'a1"
  fixes f2 :: "'syn2 \<Rightarrow> 'a2 \<Rightarrow> 'a2"
  assumes Hsl : "sup_l ls1 ls2 l1 l2"
  shows "sup_pres
    (l_map2' ls1 l1 f1)
    (l_map2' ls2 l2 f2)"
proof(rule sup_pres_intro)
  fix syn :: 'syn
  fix st1 :: 'b
  fix st2 :: 'b
  assume Hsup : "has_sup {st1, st2}"
  show "has_sup {l_map2' ls1 l1 f1 syn st1, l_map2' ls2 l2 f2 syn st2}"
    using Hsup sup_l_unfold2[OF Hsl]
    by(auto simp add: l_map2'_def split:option.splits)
qed

(*
lemma sup_l_pres :
  fixes l1 :: "('x, 'a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('x, 'a2, 'b :: Mergeable) lifting"
  fixes f1 :: "'x \<Rightarrow> 'a1 \<Rightarrow> 'a1"
  fixes f2 :: "'x \<Rightarrow> 'a2 \<Rightarrow> 'a2"
  assumes Hsl : "sup_lg l1 l2"
  shows "sup_pres
    (l_map l1 f1)
    (l_map l2 f2)"
proof(rule sup_pres_intro)
  fix syn :: 'x
  fix st1 :: 'b
  fix st2 :: 'b
  assume Hsup : "has_sup {st1, st2}"
  show "has_sup {lg_map l1 f1 syn st1, lg_map l2 f2 syn st2}"
      using Hsup sup_lg_unfold2[OF Hsl]
      by(auto simp add: lg_map_def split:option.splits)
  qed
*)


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
  assumes Hlc : "lc = \<lparr> Sem1 = (l_map2' ls1 l1 f1)
                      , Sem2 = (l_map2' ls2 l2 f2) \<rparr>" 
  assumes Hsl : "sup_l ls1 ls2 l1 l2"
  shows "lc_valid lc"
proof(-)
  have "sup_pres
    (l_map2' ls1 l1 f1)
    (l_map2' ls2 l2 f2)" using sup_l_pres[OF Hsl] by auto

  thus "lc_valid lc" by(auto simp add:Hlc lc_valid_def)
qed



lemma sup_l_comm :
  fixes ls1 :: "('x \<Rightarrow> 'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1  :: "('x1, 'a1, 'b :: Mergeableb) lifting"
  fixes l2 :: "('x2, 'a2, 'b :: Mergeableb) lifting"
  assumes H : "sup_l ls1 ls2 l1 l2"
  shows "sup_l ls2 ls1 l2 l1"
proof(rule sup_l_intro)
  fix s :: "'x"
  fix a2 :: 'a2
  fix a1 :: "'a1"
  have "{LIn1 l2 (ls2 s) a2, LIn1 l1 (ls1 s) a1} = {LIn1 l1 (ls1 s) a1, LIn1 l2 (ls2 s) a2}" by auto
  thus "has_sup {LIn1 l2 (ls2 s) a2, LIn1 l1 (ls1 s) a1}" using sup_l_unfold1[OF H, of s a1 a2] by auto
next
  fix s :: "'x"
  fix a2 :: 'a2
  fix a1 :: 'a1
  fix b1 b2 :: 'b
  assume Hs : "has_sup {b1, b2}"

  have "{b2, b1} = {b1, b2}" by auto
  hence Hs' : "has_sup {b2, b1}" using Hs by auto
  have "{LIn2 l1 (ls1 s) a1 b2, LIn2 l2 (ls2 s) a2 b1} = {LIn2 l2 (ls2 s) a2 b1, LIn2 l1 (ls1 s) a1 b2}" by auto

  thus "has_sup {LIn2 l2 (ls2 s) a2 b1, LIn2 l1 (ls1 s) a1 b2}"
    using sup_l_unfold2[OF H Hs', of s a1 a2] by auto
qed



end