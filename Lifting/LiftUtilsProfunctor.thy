theory LiftUtilsProfunctor imports  "../MergeableTc/MergeableInstances" "../MergeableTc/MergeableAList"

begin


(* lifting' is used for syntax *)
type_synonym ('a, 'b) lifting' = "('b \<Rightarrow> 'a)"

(* key abstraction used to lift semantics into larger types *)
record ('sa, 'sb, 'a, 'b) lifting =
  LSyn :: "('sb \<Rightarrow> 'sa)"
  LIn1 :: "('sa \<Rightarrow> 'a \<Rightarrow> 'b)"
  LIn2 :: "('sa \<Rightarrow> 'sb \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)" (*TODO: is 'sb appropriate here?*)
  LOut1 :: "('sb \<Rightarrow> 'b \<Rightarrow> 'a)" (* TODO: is 'sb appropriate here? *)

definition lift ::
  "('sa, 'sb, 'a, 'b) lifting \<Rightarrow>
    ('sa \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('sb \<Rightarrow> 'b \<Rightarrow> 'b)" where
"lift l sem syn st =
  (LIn2 l (LSyn l syn) syn (sem (LSyn l syn) (LOut1 l syn st)) st)"


definition l_pred :: "('sa, 'sb, 'a, 'b) lifting \<Rightarrow> ('sa \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('sb \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred t P =
  (\<lambda> s b . P (LSyn t s) (LOut1 t s b))"


(* we also want 2 notions of lifting preds over functions
   (1 for semantics only; 1 for syntax) *)

(* LOut2 or LOut1 for the second one?  *)
definition l_pred_step ::
  "('sa, 'sb, 'a, 'b) lifting \<Rightarrow>
   ('sa \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('sb \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step l P s st1 st2 =
        (P (LSyn l s) (LOut1 l s st1) (LOut1 l s st2))"


definition lifting_valid ::
  "('sa, 'sb, 'a, 'b) lifting \<Rightarrow> bool" where
"lifting_valid l =
 ((\<forall> s a .  LOut1 l s (LIn1 l (LSyn l s) a) = a) \<and>
  (\<forall> s a b . LOut1 l s (LIn2 l (LSyn l s) (s) a b) = a))"

lemma lifting_valid_intro :
  assumes H1 : "\<And> s a .  LOut1 l s (LIn1 l (LSyn l s) a) = a"
  assumes H2 : "\<And> s a b . LOut1 l s (LIn2 l (LSyn l s) (s) a b) = a"
  shows "lifting_valid l"
  using H1 H2
  by(auto simp add:lifting_valid_def)

lemma lifting_valid_unfold1 :
  assumes H : "lifting_valid l"
  shows "LOut1 l s (LIn1 l (LSyn l s) a) = a"
  using H by (auto simp add:lifting_valid_def)

lemma lifting_valid_unfold2 :
  assumes H : "lifting_valid l"
  shows "LOut1 l s (LIn2 l (LSyn l s) (s) a b) = a"
  using H by (auto simp add:lifting_valid_def)

lemma pred_lift :
  fixes l :: "('sa, 'sb, 'a, 'b) lifting"
  fixes P :: "('sa \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  fixes sem :: "('sa \<Rightarrow> 'a \<Rightarrow> 'a)"
  fixes sa :: "'sa"
  fixes sb :: "'sb"
  fixes a :: "'a"
  fixes b :: "'b"
  assumes Hv : "lifting_valid l"
  assumes Hsyn : "LSyn l sb = sa"
  assumes Hsem : "LOut1 l sb b = a" 
  assumes HP : "P sa a (sem sa a)"
  shows "l_pred_step l P sb
      b
      (lift l sem sb b)"
  using Hsyn Hsem HP lifting_valid_unfold2[OF Hv] 
  apply(cases l; auto simp add:l_pred_step_def lift_def)
  done

definition synmap ::
  "('sc \<Rightarrow> 'sb) \<Rightarrow>
   ('sa, 'sb, 'a, 'b) lifting \<Rightarrow>
   ('sa, 'sc, 'a, 'b) lifting" where
"synmap f l =
  \<lparr> LSyn = (\<lambda> sc . LSyn l (f sc))
  , LIn1 = LIn1 l
  , LIn2 = (\<lambda> sa sc a b . LIn2 l sa (f sc) a b)
  , LOut1 = (\<lambda> sc b .  LOut1 l (f sc) b)\<rparr>"

lemma lifting_valid_synmap :
  assumes H : "lifting_valid (l :: ('a, 'sb, 'a, 'b) lifting)"
  shows "lifting_valid (synmap (f :: ('sc \<Rightarrow> 'sb)) l)"
proof(rule lifting_valid_intro)
  fix s :: "'sc"
  fix a :: 'a
  show "LOut1 (synmap f l) s (LIn1 (synmap f l) (LSyn (synmap f l) s) a) = a"
    using lifting_valid_unfold1[OF H]
    by(auto simp add:synmap_def)
next
  fix s :: "'sc"
  fix a :: 'a
  fix b :: 'b
  show "LOut1 (synmap f l) s (LIn2 (synmap f l) (LSyn (synmap f l) s) s a b) = a"
    using lifting_valid_unfold2[OF H]
    by(auto simp add:synmap_def)
qed

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
  "('sa1, 'sb, 'a1, ('b :: Pord)) lifting \<Rightarrow>
   ('sa2, 'sb, 'a2, ('b :: Pord)) lifting \<Rightarrow>
   bool" where
"sup_l l1 l2 =
  (\<forall> s a1 a2 b1 b2 .
    has_sup {LIn1 l1 (LSyn l1 s) a1, LIn1 l2 (LSyn l2 s) a2} \<and>
    (has_sup {b1, b2} \<longrightarrow> has_sup {LIn2 l1 (LSyn l1 s) s a1 b1, LIn2 l2 (LSyn l2 s) s a2 b2}))"

lemma sup_l_intro :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b :: Pord) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b :: Pord) lifting"
  assumes H1 : "\<And> s a1 a2 . has_sup {LIn1 l1 (LSyn l1 s) a1, LIn1 l2 (LSyn l2 s) a2}"
  assumes H2 : "\<And> s a1 a2 b1 b2 . has_sup {b1, b2} \<Longrightarrow> has_sup {LIn2 l1 (LSyn l1 s) s a1 b1, LIn2 l2 (LSyn l2 s) s a2 b2}"
  shows "sup_l l1 l2" using H1 H2
  by(auto simp add:sup_l_def)

lemma sup_l_unfold1 :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b :: Pord) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b :: Pord) lifting"
  assumes H : "sup_l l1 l2"  
  shows "has_sup {LIn1 l1 (LSyn l1 s) a1, LIn1 l2 (LSyn l2 s) a2}"
  using H   by(auto simp add:sup_l_def)

lemma sup_l_unfold2 :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b :: Pord) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b :: Pord) lifting"
  assumes Hs : "sup_l l1 l2"
  assumes Hb : "has_sup {b1, b2}"
  shows "has_sup {LIn2 l1 (LSyn l1 s) s a1 b1, LIn2 l2 (LSyn l2 s) s a2 b2}"
  using  Hb Hs
  by(auto simp add:sup_l_def)


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

lemma sup_l_synmap :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b :: Mergeable) lifting"
  fixes f :: "'sc \<Rightarrow> 'sb"
  assumes Hsl : "sup_l l1 l2"
  shows "sup_l (synmap f l1) (synmap f l2)"
proof(rule sup_l_intro)
  fix s :: 'sc
  fix a1 :: 'a1
  fix a2 :: 'a2
  show "has_sup
        {LIn1 (synmap f l1) (LSyn (synmap f l1) s) a1,
         LIn1 (synmap f l2) (LSyn (synmap f l2) s) a2}" using sup_l_unfold1[OF Hsl]
    by(auto simp add:synmap_def)
next
  fix s :: 'sc
  fix a1 :: 'a1
  fix b1 :: 'b
  fix a2 :: 'a2
  fix b2 :: 'b
  assume Hb : "has_sup {b1, b2}"
  show "has_sup
        {LIn2 (synmap f l1) (LSyn (synmap f l1) s) s a1 b1,
         LIn2 (synmap f l2) (LSyn (synmap f l2) s) s a2 b2}"
using sup_l_unfold2[OF Hsl] Hb
  by(auto simp add:synmap_def)
qed

(* TODO: what can we say about sup in the case where the syntaxes might not
be the same to begin with? *)

lemma sup_l_pres :
  fixes l1 :: "('sa1, 'sb, 'a1, 'b :: Mergeable) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b :: Mergeable) lifting"
  fixes f1 :: "'sa1 \<Rightarrow> 'a1 \<Rightarrow> 'a1"
  fixes f2 :: "'sa2 \<Rightarrow> 'a2 \<Rightarrow> 'a2"
  assumes Hsl : "sup_l l1 l2"
  shows "sup_pres
    (lift l1 f1)
    (lift l2 f2)"
proof(rule sup_pres_intro)
  fix syn :: 'sb
  fix st1 :: 'b
  fix st2 :: 'b
  assume Hsup : "has_sup {st1, st2}"
  show "has_sup {lift l1 f1 syn st1, lift l2 f2 syn st2}"
    using Hsup sup_l_unfold2[OF Hsl]
    by(auto simp add: lift_def split:option.splits)
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
  assumes Hlc : "lc = \<lparr> Sem1 = (lift l1 f1)
                      , Sem2 = (lift l2 f2) \<rparr>" 
  assumes Hsl : "sup_l l1 l2"
  shows "lc_valid lc"
proof(-)
  have "sup_pres
    (lift l1 f1)
    (lift l2 f2)" using sup_l_pres[OF Hsl] by auto

  thus "lc_valid lc" by(auto simp add:Hlc lc_valid_def)
qed



lemma sup_l_comm :
  fixes l1  :: "('sa1, 'sb, 'a1, 'b :: Mergeableb) lifting"
  fixes l2 :: "('sa2, 'sb, 'a2, 'b :: Mergeableb) lifting"
  assumes H : "sup_l l1 l2"
  shows "sup_l l2 l1"
proof(rule sup_l_intro)
  fix s :: "'sb"
  fix a2 :: 'a2
  fix a1 :: "'a1"
  have "{LIn1 l2 (LSyn l2 s) a2, LIn1 l1 (LSyn l1 s) a1} = {LIn1 l1 (LSyn l1 s) a1, LIn1 l2 (LSyn l2 s) a2}" by auto
  thus "has_sup {LIn1 l2 (LSyn l2 s) a2, LIn1 l1 (LSyn l1 s) a1}" using sup_l_unfold1[OF H, of s a1 a2] by auto
next
  fix s :: "'sb"
  fix a2 :: 'a2
  fix a1 :: 'a1
  fix b1 b2 :: 'b
  assume Hs : "has_sup {b1, b2}"

  have "{b2, b1} = {b1, b2}" by auto
  hence Hs' : "has_sup {b2, b1}" using Hs by auto
  have "{LIn2 l1 (LSyn l1 s) s a1 b2, LIn2 l2 (LSyn l2 s) s a2 b1} = {LIn2 l2 (LSyn l2 s) s a2 b1, LIn2 l1 (LSyn l1 s) s a1 b2}" by auto

  thus "has_sup {LIn2 l2 (LSyn l2 s) s a2 b1, LIn2 l1 (LSyn l1 s) s a1 b2}"
    using sup_l_unfold2[OF H Hs', of s a1 a2] by auto
qed



end