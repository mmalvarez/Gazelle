theory Lang_Comp imports Lifter
begin


(* TODO: how does sup_l fit into this?
   the reason i thought we needed the (stronger) statement
   that LUBs are preserved (rather than
   just "inputs are equal \<Rightarrow> outputs have LUBs) was that
   it seemed like you needed this to be able to relate
   the Base elements of liftings
*)
type_synonym ('a, 'b) langcomp =
  "('a \<Rightarrow> 'b \<Rightarrow> 'b) * ('a \<Rightarrow> 'b \<Rightarrow> 'b)"

abbreviation Sem1 ::
  "('a, 'b) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"Sem1 \<equiv> fst"

abbreviation Sem2 ::
  "('a, 'b) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"Sem2 \<equiv> snd"

type_synonym ('a, 'b) langcomps =
  "('a \<Rightarrow> 'b \<Rightarrow> 'b) list"

(* idea: commutativity should mean that the ordering of composition doesn't matter *)
fun pcomps :: "('a, 'b :: Mergeable) langcomps \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomps [] a b = b"
| "pcomps [lh] a b = [^ lh a b, b ^]"
| "pcomps [l1, l2] a b =
  [^ [^ l1 a b, l2 a b ^], b^]"
| "pcomps (lh#lt) a b =
   [^ [^ lh a b, pcomps lt a b ^], b ^]"

(* simpler version - but i'm unsure if this handles the binary case correctly. *)
fun pcomps' :: "('a, 'b :: Mergeable) langcomps \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomps' [] a b = b"
| "pcomps' [lh] a b = lh a b"
| "pcomps' (lh#lt) a b =
   [^ lh a b, pcomps' lt a b ^]"

(* pointwise/ordering sensitivity. how exactly to handle this?
   do we need to care about the order? *)
(*
definition sups_pres ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> bool" where
"sups_pres Sf =
  (\<forall> syn :: 'a .
    (\<forall> Sx :: 'b set .
      has_sup Sx \<longrightarrow>
       
      has_sup S'
    
*)    

(* we want either distinctness for Fsx, or finiteness
   finiteness might be easier. but also results in a stronger property, since
   it allows for merging f with itself. but maybe this is ok. such a thing should
   always be possible.
 *)
inductive sups_pres :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> bool" where
"\<And> Fs :: ('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set .
 (\<And> Fsx :: (('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) * 'b) set .
  \<And> syn :: 'a .
  finite Fsx \<Longrightarrow>
  Fs = fst ` Fsx \<Longrightarrow>
  has_sup (snd ` Fsx) \<Longrightarrow>
  has_sup ((\<lambda> fx . (case fx of (f, x) \<Rightarrow> f syn x)) ` Fsx)) \<Longrightarrow>
 sups_pres Fs"

(* removeAll *)


(* sup_pres captures the idea that a function preserves sups *)
definition sup_pres ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"sup_pres f1 f2 =
 (\<forall> syn :: 'a .
   \<forall> st1 st2 :: 'b .
     has_sup {st1, st2} \<longrightarrow>
     has_sup {f1 syn st1, f2 syn st2})"

lemma sup_presD :
  fixes f1 f2 :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b)"
  fixes syn :: 'a
  fixes st1 st2 :: 'b
  assumes H : "sup_pres f1 f2"
  assumes Hsup : "has_sup {st1, st2}"
  shows "has_sup {f1 syn st1, f2 syn st2}" using H Hsup
  by(auto simp add:sup_pres_def)

lemma sup_presI :
  fixes f1 f2 :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b)"
  assumes H : "\<And> (syn :: 'a) (st1 :: 'b) (st2 :: 'b) .
                  has_sup {st1, st2} \<Longrightarrow> has_sup {f1 syn st1, f2 syn st2}"
  shows "sup_pres f1 f2" using H
  by(auto simp add:sup_pres_def)

(* generalize to mergeable syntax - probably this isn't useful. *)
definition sup_pres' ::
  "(('a :: Mergeable) \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"sup_pres' f1 f2 =
 (\<forall> syn1 syn2 :: 'a .
   \<forall> st1 st2 :: 'b .
     has_sup {st1, st2} \<longrightarrow>
     has_sup {syn1, syn2} \<longrightarrow>
     has_sup {f1 syn1 st1, f2 syn2 st2})"

(* sup_l captures the idea that liftings "preserve" suprema*)
definition sup_l ::
  "('x \<Rightarrow> 'x1) \<Rightarrow>
   ('x \<Rightarrow> 'x2) \<Rightarrow>
   ('x1, 'a1, ('b :: Pord), 'z1) lifting_scheme \<Rightarrow>
   ('x2, 'a2, ('b :: Pord), 'z2) lifting_scheme \<Rightarrow>
   bool" where
"sup_l ls1 ls2 l1 l2 =
  (\<forall> s a1 a2 b1 b2 .
    has_sup {LBase l1 (ls1 s), LBase l2 (ls2 s)} \<and>
    (has_sup {b1, b2} \<longrightarrow> has_sup {LUpd l1 (ls1 s) a1 b1, LUpd l2 (ls2 s) a2 b2}))"

lemma sup_lI :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Pord, 'z2) lifting_scheme"
  assumes H1 : "\<And> s a1 a2 . has_sup {LBase l1 (ls1 s) , LBase l2 (ls2 s) }"
  assumes H2 : "\<And> s a1 a2 b1 b2 . has_sup {b1, b2} \<Longrightarrow> has_sup {LUpd l1 (ls1 s) a1 b1, LUpd l2 (ls2 s) a2 b2}"
  shows "sup_l ls1 ls2 l1 l2" using H1 H2
  by(auto simp add:sup_l_def)

lemma sup_lDB :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Pord, 'z2) lifting_scheme"
  assumes H : "sup_l ls1 ls2 l1 l2"  
  shows "has_sup {LBase l1 (ls1 s), LBase l2 (ls2 s) }"
  using H   by(auto simp add:sup_l_def)

lemma sup_lDI :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Pord, 'z2) lifting_scheme"
  assumes Hs : "sup_l ls1 ls2 l1 l2"
  assumes Hb : "has_sup {b1, b2}"
  shows "has_sup {LUpd l1 (ls1 s) a1 b1, LUpd l2 (ls2 s) a2 b2}"
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

(* TODO: need to adjust this to account for new definition
   of lifting using option *)

lemma sup_l_pres :
  fixes ls1 :: "'syn \<Rightarrow> 'syn1"
  fixes ls2 :: "'syn \<Rightarrow> 'syn2"
  fixes l1 :: "('syn1, 'a1, 'b :: Mergeable, 'z1) lifting_scheme"
  fixes l2 :: "('syn2, 'a2, 'b :: Mergeable, 'z2) lifting_scheme"
  fixes f1 :: "'syn1 \<Rightarrow> 'a1 \<Rightarrow> 'a1"
  fixes f2 :: "'syn2 \<Rightarrow> 'a2 \<Rightarrow> 'a2"
  assumes Hsl : "sup_l ls1 ls2 l1 l2"
  shows "sup_pres
    (lift_map_s ls1 l1 f1)
    (lift_map_s ls2 l2 f2)"
proof(rule sup_presI)
  fix syn :: 'syn
  fix st1 :: 'b
  fix st2 :: 'b
  assume Hsup : "has_sup {st1, st2}"
  show "has_sup {lift_map_s ls1 l1 f1 syn st1, lift_map_s ls2 l2 f2 syn st2}"

    using Hsup sup_lDI[OF Hsl] sup_lDI[OF Hsl]
    by(auto split:option.splits)
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

(* composition doesn't matter for valid LC *)
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

lemma ub_union1 :
  assumes Hsup1 : "is_ub S1 x1"
  assumes Hsup2 : "is_ub S2 x2"
  assumes HsupU : "is_ub {x1, x2} x'"
  shows "is_ub (S1 \<union> S2) x'"
proof(rule is_ubI)
  fix x
  assume Hx : "x \<in> S1 \<union> S2"
  then consider (1) "x \<in> S1" | (2) "x \<in> S2" by auto
  then show "x <[ x'"
  proof cases
    case 1
    then have Leq1 : "x <[ x1" using Hsup1 by(auto simp add: is_ub_def)
    have Leq2 : "x1 <[ x'" using HsupU by(auto simp add: is_ub_def)
    then show ?thesis using leq_trans[OF Leq1 Leq2] by auto
  next
    case 2
    then have Leq1 : "x <[ x2" using Hsup2 by(auto simp add: is_ub_def)
    have Leq2 : "x2 <[ x'" using HsupU by(auto simp add: is_ub_def)
    then show ?thesis using leq_trans[OF Leq1 Leq2] by auto
  qed
qed

lemma sup_union1 :
  assumes Hsup1 : "is_sup S1 x1"
  assumes Hsup2 : "is_sup S2 x2"
  assumes HsupU : "is_sup {x1, x2} x'"
  shows "is_sup (S1 \<union> S2) x'"
proof(rule is_supI)
  fix x
  assume Hx : "x \<in> S1 \<union> S2"
  consider (1) "x \<in> S1" |
           (2) "x \<in> S2" using Hx by auto
  then show "x <[ x'"
  proof cases
    case 1
    then show ?thesis using is_supD1[OF Hsup1 1] is_supD1[OF HsupU, of x1]
      by(auto simp add: leq_trans[of x x1])
  next
    case 2
    then show ?thesis using is_supD1[OF Hsup2 2] is_supD1[OF HsupU, of x2]
      by(auto simp add: leq_trans[of x x2])
  qed
next
  fix x'a
  assume Hx'a : "is_ub (S1 \<union> S2) x'a"

  have "is_ub S1 x'a" using Hx'a
    by(auto simp add: is_ub_def)

  hence Ub1: "x1 <[ x'a"
    using is_supD2[OF Hsup1] by auto

  have "is_ub S2 x'a" using Hx'a
    by(auto simp add: is_ub_def)

  hence Ub2: "x2 <[ x'a"
    using is_supD2[OF Hsup2] by auto

  have "is_ub {x1, x2} x'a" using Ub1 Ub2
    by(auto simp add: is_ub_def)

  thus "x' <[ x'a"
    using is_supD2[OF HsupU] by auto
qed


lemma ub_union2 :
  assumes Hsup1 : "is_sup S1 x1"
  assumes Hsup2 : "is_sup S2 x2" 
  assumes HsupU : "is_ub (S1 \<union> S2) x'"
  shows HsupU : "is_ub {x1, x2} x'"
proof(rule is_ubI)
  fix x

  assume Hx : "x \<in> {x1, x2}"

  then consider (1) "x = x1" | (2) "x = x2"
    by auto

  then show "x <[ x'"
  proof cases
    case 1
    have "is_ub S1 x'"
      using HsupU by(auto simp add: is_ub_def)
    thus ?thesis using is_supD2[OF Hsup1] 1 by auto
  next
    case 2
    have "is_ub S2 x'"
      using HsupU by(auto simp add: is_ub_def)
    thus ?thesis using is_supD2[OF Hsup2] 2 by auto
  qed
qed

lemma sup_union2 :
  assumes Hsup1 : "is_sup S1 x1"
  assumes Hsup2 : "is_sup S2 x2"
  assumes HsupU : "is_sup (S1 \<union> S2) x'"
  shows "is_sup {x1, x2} x'" 
proof(rule is_supI)
  fix x
  assume Hx : "x \<in> {x1, x2}"

  then consider (1) "x = x1" | (2) "x = x2"
    by auto

  then show "x <[ x'"
  proof cases
    case 1
    have "is_ub S1 x'"
      using is_supD1[OF HsupU] by(auto simp add: is_ub_def)
    thus ?thesis using is_supD2[OF Hsup1] 1 by auto
  next
    case 2
    have "is_ub S2 x'"
      using is_supD1[OF HsupU] by(auto simp add: is_ub_def)
    thus ?thesis using is_supD2[OF Hsup2] 2 by auto
  qed
next
  fix x'a
  assume Hx'a : "is_ub {x1, x2} x'a"

  have "is_ub (S1 \<union> S2) x'a"
  proof(rule is_ubI)
    fix x
    assume Hx : "x \<in> S1 \<union> S2"
    then consider (1) "x \<in> S1" | (2) "x \<in> S2" by auto
    then show "x <[ x'a"
    proof cases
      case 1
      hence Leq1 : "x <[ x1" using is_supD1[OF Hsup1] by auto
      have Leq2 : "x1 <[ x'a" using Hx'a by(auto simp add: is_ub_def)
      show ?thesis
        using leq_trans[OF Leq1 Leq2] by auto
    next
      case 2
      hence Leq1 : "x <[ x2" using is_supD1[OF Hsup2] by auto
      have Leq2 : "x2 <[ x'a" using Hx'a by(auto simp add: is_ub_def)
      show ?thesis
        using leq_trans[OF Leq1 Leq2] by auto
    qed
  qed

  thus "x' <[ x'a"
    using is_supD2[OF HsupU] by auto
qed
    
lemma finite_complete :
  fixes S :: "('b :: Pordc) set"
  fixes x :: "'b"
  assumes Hfin : "finite S"
  assumes Hx : "x \<in> S" 
  assumes Hub : "is_ub S sub"
  shows "\<exists> ssup . is_sup S ssup" using assms
proof(induction S arbitrary: x sub)
  case empty
  then show ?case 
    by auto
next
  case (insert x1 S')
  show ?case
  proof(cases "S' = {}")
    case True
    then have "is_sup (insert x1 S') x1"
      by(auto simp add: is_sup_def is_ub_def is_least_def leq_refl)
    thus ?thesis by auto
  next
    case False
    then obtain x' where X': "x' \<in> S'" by auto
    have Ub1 : "is_ub S' sub" using insert
      by(auto simp add: is_ub_def)
    have Union : "is_ub ({x1} \<union> S') sub" using insert by auto

    obtain s'sup where S'sup : "is_sup S' s'sup"
      using insert.IH[OF X' Ub1] by auto

    have X1sup : "is_sup {x1} x1" by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

    have Pair : "has_ub ({x1, s'sup})"
      using ub_union2[OF X1sup S'sup Union]
      by(auto simp add: has_ub_def)

    obtain ssup where Ssup : "is_sup {x1, s'sup} ssup"
      using complete2[OF Pair] by(auto simp add: has_sup_def)

    show ?thesis using sup_union1[OF X1sup S'sup Ssup] by auto
  qed
qed

lemma has_sup_subset :
  fixes S S' :: "('b :: Pordc) set"
  assumes Hfin : "finite S"
  assumes H : "is_sup S s"
  assumes Hsub : "S' \<subseteq> S"
  assumes Hnemp : "x \<in> S'"
  shows "has_sup S'"
proof(-)
  have Fin' : "finite S'" using rev_finite_subset[OF Hfin Hsub]
    by(auto)

  have Ub' : "is_ub S' s"
  proof(rule is_ubI)
    fix x
    assume "x \<in> S'"
    hence "x \<in> S" using Hsub by auto
    thus "x <[ s"
      using is_supD1[OF H] by auto
  qed

  obtain s' where "is_sup S' s'"
    using finite_complete[OF Fin' Hnemp Ub'] by auto

  thus "has_sup S'" by(auto simp add: has_sup_def)
qed


lemma sups_pres_subset :
  fixes Fs :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set"
  assumes H : "sups_pres Fs"
  assumes Hfin : "finite Fs"
  assumes Hsub : "Fs' \<subseteq> Fs"
  assumes Hnemp : "f \<in> Fs'"
  shows "sups_pres Fs'" using assms
proof(induction arbitrary: f Fs' rule: sups_pres.induct)
  case (1 Fs)
  show ?case 
  proof(rule sups_pres.intros)
    fix Fsx' :: "(('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) * 'b) set"
    fix syn :: 'a
    assume Hfin' : "finite Fsx'"
    assume H' : "Fs' = fst ` Fsx'"
    assume Hsup : "has_sup (snd ` Fsx')" 
    
    obtain f_arb a where Hfa : 
      "(f_arb, a) \<in> Fsx'" using "1"(3) "1"(4) H' by(auto)
    
    obtain Rest where Rest : "Fs' \<union> Rest = Fs" using 1 by blast

    have Rest' : "fst ` (\<lambda>x. (x, a)) ` Rest = Rest" unfolding image_comp
      by(auto)

    have Fs' : "Fs = fst ` (Fsx' \<union> (\<lambda> x . (x, a)) ` Rest)" unfolding Set.image_Un using Hfa Rest Rest' H' 
      by(auto)

    have Snd : "snd ` (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest) = snd ` Fsx'"
    proof(cases "Rest = {}")
      case True
      then show ?thesis unfolding image_Un image_comp by auto
    next
      case False
      hence A : "snd ` ((\<lambda>x. (x, a)) ` Rest) = {a}" unfolding image_comp by auto

      have A_in : "a \<in> snd ` Fsx'" using Set.imageI[OF Hfa, of snd] by auto

      then show ?thesis unfolding image_Un image_comp using A by auto
    qed
    have Sup' : "has_sup (snd ` (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest))"
      unfolding Snd using Hsup by auto

    have Rfin : "finite Rest" using Rest "1"(2) by auto

    have Fin' : "finite (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest)" using Hfin' Rfin
      unfolding image_Un
      by(auto)

    hence Fin'' : "finite ((\<lambda>(f, y). f syn y) ` (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest))" by auto

    have Conc' : "has_sup ((\<lambda>(f, y). f syn y) ` (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest))"
      using "1.hyps"[OF Fin' Fs' Sup'] H' Hsup by auto

    then obtain supr where Supr :
      "is_sup ((\<lambda>(f, y). f syn y) ` (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest)) supr"
      by(auto simp add: has_sup_def)

    have Subset : "(\<lambda>(f, y). f syn y) ` (Fsx') \<subseteq> (\<lambda>(f, y). f syn y) ` (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest)"
      unfolding image_comp by auto

    have Nemp : "(f_arb syn a) \<in> (\<lambda>(f, y). f syn y) ` Fsx'"
      using Hfa by auto

    show "has_sup ((\<lambda>(f, y). f syn y) ` Fsx')"
      using has_sup_subset[OF Fin'' Supr Subset Nemp]
      by(auto)
  qed
qed
(*
proof(induction rule: sups_pres.induct)
  case (1 Fs)
  then show ?case
    
    
qed
  *)

lemma bsup_idem :
  "[^ x, x ^] = x"
proof-
  have 0: "is_sup {x, x} x"
    by(auto simp add: is_sup_def is_ub_def is_least_def leq_refl)
  have 1: "is_bsup x x [^x, x^]" using bsup_spec by auto

  show "[^ x, x ^] = x"
    using is_sup_unique[OF 0 bsup_sup[OF 0 1]] by auto
qed

lemma bsup_base_leq :
  assumes H : "x <[ y"
  shows "[^ x, y ^] = y"
proof-
  have 0 : "is_sup {x, y} y" using H
    by(auto simp add: has_sup_def is_sup_def is_least_def is_ub_def leq_refl)

  have 1: "is_bsup x y [^ x, y ^]" using bsup_spec by auto

  have 2 : "is_sup {x, y} [^ x, y ^]" using bsup_sup[OF 0 1] by auto

  show "[^ x, y ^] = y"
    using is_sup_unique[OF 0 2] by auto
qed

lemma bsup_base_eq :
  "[^ x, [^ x, y ^]^] = [^ x, y ^]"
proof-
  have 0: "x <[ [^ x, y ^]"
    using is_bsup_unfold1[OF bsup_spec[of x y]] by auto

  show "[^ x, [^ x, y ^]^] = [^ x, y ^]"
    using bsup_base_leq[OF 0] by auto
qed

lemma bsup_arg_eq :
  "[^ [^ x, y ^], y ^] = [^ x, y ^]"
proof-
  have Eq1 : "[^ x, y ^] <[ [^ [^ x, y ^], y ^]"
    using is_bsup_unfold1[OF bsup_spec] by auto

  have Eq2 : "[^ [^ x, y ^], y ^] <[ [^ x, y ^]"
    using bsup_assoc_fact2[of x y y] unfolding bsup_idem[of "[^ x, y ^]"] by auto

  show "[^ [^ x, y ^], y ^] = [^ x, y ^]"
    using leq_antisym[OF Eq2 Eq1] by auto
qed

lemma sup_singleton :
  "is_sup {x} x"
  by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

lemma bsup_assoc3 :
  assumes H : "has_sup {a, b, c}"
  shows "[^ [^ a, b ^], c ^] = [^ a, [^ b, c ^]^]"
proof-
  obtain s_abc where ABC : "is_sup {a, b, c} s_abc" using H by (auto simp add: has_sup_def)

  obtain s_ab where AB : "is_sup {a, b} s_ab" using has_sup_subset[OF _ ABC, of "{a, b}"]
    by(auto simp add: has_sup_def)

  have bAB : "s_ab = [^ a, b ^]"
    using is_sup_unique[OF bsup_sup[OF AB bsup_spec] AB] by auto

  obtain s_bc where BC : "is_sup {b, c} s_bc" using has_sup_subset[OF _ ABC, of "{b, c}"]
    by(auto simp add: has_sup_def)

  have bBC : "s_bc = [^ b, c ^]"
    using is_sup_unique[OF bsup_sup[OF BC bsup_spec] BC] by auto
  
  have Help1 : "{a, b} \<union> {c} = {a, b, c}" by auto

  have "is_sup {s_ab, c} s_abc"
    using  sup_union2[OF AB sup_singleton[of c], of s_abc] ABC unfolding Help1 by auto

  hence LHS': "is_sup {[^ a, b ^], c} s_abc"
    unfolding bAB by auto

  have LHS : "[^ [^ a, b ^], c ^] = s_abc"
    using is_sup_unique[OF bsup_sup[OF LHS' bsup_spec] LHS'] by auto

  have Help2 : "{b, c} \<union> {a} = {a, b, c}" by auto

  have Help3 : "{[^ b, c ^], a} = {a, [^ b, c ^]}" by auto

  have "is_sup {s_bc, a} s_abc"
    using  sup_union2[OF BC sup_singleton[of a], of s_abc] ABC unfolding Help2 by auto

  hence RHS': "is_sup {a, [^ b, c ^]} s_abc"
    unfolding bBC Help3 by auto

  have RHS : "[^ a, [^ b, c ^] ^] = s_abc"
    using is_sup_unique[OF bsup_sup[OF RHS' bsup_spec] RHS'] by auto

  show "[^ [^ a, b ^], c ^] = [^ a, [^ b, c ^] ^]" using LHS RHS by auto
qed


lemma pcomps'_cons_same :
  shows "pcomps' (x#x#t) = pcomps' (x#t)"
proof(induction t arbitrary: x)
  case Nil
  then show ?case 
    by(auto simp add: bsup_idem)
next
  case (Cons a1 t1)
  then show ?case unfolding pcomps'.simps bsup_base_eq
    by auto
qed
(*
lemma pcomps_cons_same :
  shows "pcomps (x#x#t) = pcomps (x#t)"
proof(induction t arbitrary: x)
  case Nil
  then show ?case 
    by(auto simp add: bsup_idem)
next
  case (Cons a1 t1)
  then show ?case 
  proof(cases t1)
    case Nil' : Nil
    show ?thesis
      unfolding pcomps.simps Nil'
    proof(rule ext; rule ext) 
      fix syn state

      have Eq0 : "[^ x syn state, a1 syn state ^] <[ [^ [^ x syn state, a1 syn state ^], state ^]"
        using is_bsup_unfold1[OF bsup_spec] by auto

      have Eq1 : "x syn state <[ [^ x syn state, a1 syn state ^]"
        using is_bsup_unfold1[OF bsup_spec] by auto

      have Eq2 : "[^ x syn state, [^ [^ x syn state, a1 syn state ^], state ^] ^] = [^ [^ x syn state, a1 syn state ^], state ^]"
        using bsup_base_leq[OF leq_trans[OF Eq1 Eq0]] by auto

      show "[^ [^ x syn state, [^ [^ x syn state, a1 syn state ^], state ^] ^], state ^] = 
            [^ [^ x syn state, a1 syn state ^], state ^]"
        unfolding Eq2 bsup_arg_eq by auto
    qed
  next
    case Cons' : (Cons a2 t2)
    show ?thesis unfolding pcomps.simps Cons'
    proof(rule ext; rule ext) 
      fix syn state

      have Eq0 : "[^ x syn state, pcomps (a1 # a2 # t2) syn state ^] <[
                  [^ [^ x syn state, pcomps (a1 # a2 # t2) syn state ^], state ^]"
        using is_bsup_unfold1[OF bsup_spec] by auto

      have Eq1 : "x syn state <[ [^ x syn state, pcomps (a1 # a2 # t2) syn state ^]"
        using is_bsup_unfold1[OF bsup_spec] by auto

      have Eq2 : "[^ x syn state, [^ [^ x syn state, pcomps (a1 # a2 # t2) syn state ^], state ^] ^] = 
                  [^ [^ x syn state, pcomps (a1 # a2 # t2) syn state ^], state ^]"
        using bsup_base_leq[OF leq_trans[OF Eq1 Eq0]] by auto

      show "[^ [^ x syn state, [^ [^ x syn state, pcomps (a1 # a2 # t2) syn state ^], state ^] ^], state ^] = 
            [^ [^ x syn state, pcomps (a1 # a2 # t2) syn state ^], state ^]"
        unfolding Eq2 bsup_arg_eq by auto
    qed
  qed
qed
*)
(* need a stronger hypothesis here *)
(*
lemma pcomps_comm :
  assumes Hp : "sups_pres ({a, b} \<union> set t)"
  shows "pcomps (a#b#t) = pcomps(b#a#t)" using assms
(* cases probably suffices here - either that or this
   does not hold inductively. *)
proof(induction t arbitrary: a b)
  case Nil
  show ?case
  proof(rule ext; rule ext)
    fix syn state

    have "has_sup { a syn state, b syn state}" using Nil(1)
    proof(cases rule: sups_pres.cases)
      case 1

      have "is_sup {state} state" by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

      hence Stsup : "has_sup {state}" by(auto simp add: has_sup_def)

      show ?thesis 
        using "1"[of "{(a, state), (b, state)}"] Stsup
        by(auto)
    qed

    hence Comm : "[^ a syn state, b syn state ^] =  [^ b syn state, a syn state ^]"
      using bsup_comm by auto

    show "pcomps [a, b] syn state = pcomps [b, a] syn state"
      unfolding pcomps.simps Comm by auto
  qed
next
  case (Cons c list)
  show ?case
  proof(rule ext; rule ext)
    fix syn state

    have Hsup : "has_sup { a syn state, b syn state}" using Cons(2)
    proof(cases rule: sups_pres.cases)
      case 1

      have "is_sup {state} state" by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

      hence Stsup : "has_sup {state}" by(auto simp add: has_sup_def)

      show ?thesis using "1"
        using "1"[of "{(a, state), (b, state)}"] Stsup
        by(auto)
    qed

    hence Comm : "[^ a syn state, b syn state ^] =  [^ b syn state, a syn state ^]"
      using bsup_comm by auto

  
    show "pcomps (a # b # c # list) syn state = pcomps (b # a # c # list) syn state"
    proof(cases list)
      case Nil' : Nil
      then show ?thesis 
(* is this true? *)
        apply(auto)
    next
      case Cons' : (Cons d list')
      then show ?thesis sorry
    qed
      unfolding pcomps.simps  
  apply(cases list; simp)
*)

(*
lemma pcomps_unique :
  assumes Hp : "sups_pres (set t)"
  assumes H : "x \<in> set t"
  shows "pcomps (x#t) = pcomps t" using assms
proof(induction t arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a1 t1)
  then show ?case 
  proof(cases "x = a1")
    case True
    show ?thesis unfolding True using pcomps_cons_same by auto
  next
    case False
    then have Xin : "x \<in> set t1" using Cons.prems by auto

    have Fin : "finite (set (a1 # t1))" by blast

    have T1_pres : "sups_pres (set t1)" using Cons.prems
        sups_pres_subset[OF Cons.prems(1) Fin _ Xin] by auto

    show ?thesis
      using Cons.IH[OF T1_pres Xin]
      sorry
  qed
qed
*) 

lemma sups_pres_pair :
  assumes Hp : "sups_pres {x1, x2}"
  shows "has_sup {x1 syn state, x2 syn state}" using assms
proof(cases rule: sups_pres.cases)
  case 1

  have "has_sup {state}" using sup_singleton[of state]
    by(auto simp add: has_sup_def)

  then show ?thesis using 1[of "{(x1, state), (x2, state)}" syn]
    by(auto)
qed

(*
(* this is the key lemma that characterizes sups_pres.
   in particular, it should imply that we can arbitrarily reorder
   elements in the list.
   it should also allow arbitrary reassociation because of
   the subset-laws we have proven about sup. *)
lemma sups_pres_pcomps_sup :
  assumes Hp : "sups_pres (set l)"
  assumes Hnemp : "l \<noteq> []"
  shows "is_sup ((\<lambda> f . f syn sem) ` (set l)) (pcomps' l syn sem)" using assms
proof (induction l arbitrary: syn sem)
  case Nil
  then show ?case by auto
next
  case (Cons h1 t1)
  show ?case 
  proof(cases t1)
    case Nil' : Nil
    then show ?thesis by(auto simp add: sup_singleton)
  next
    case Cons' : (Cons h2 t2)

    have SP : "sups_pres (set t1)"
      using sups_pres_subset[OF Cons.prems(1), of "set t1"] Cons' by auto

    have Sup : "is_sup ((\<lambda>f. f syn sem) ` set t1) (pcomps' t1 syn sem)"
      using Cons.IH[OF SP, of syn sem] Cons' by( auto)

    have HSup : "is_sup {h1 syn sem} (h1 syn sem)" using sup_singleton by auto

    have Conc' : "has_sup {h1 syn sem, pcomps' t1 syn sem}"
    proof(cases rule: sups_pres.cases[OF Cons(2)])
      case (1 Fs)

      have Eq1 : "fst ` set (map (\<lambda> f . (f, sem))(h1#t1)) = set (h1#t1)" 
        unfolding List.image_set
        by(auto)

      have Eq2 : "(snd ` set (map (\<lambda>f. (f, sem)) (h1 # t1))) = {sem}"
        unfolding List.image_set
        by auto

      have Eq3 : "(\<lambda>(f, y). f syn y) ` set (map (\<lambda>f. (f, sem)) (h1 # t1)) =
                  {h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1" 
        by(auto)

      have Sing : "has_sup {sem}"
        using sup_singleton[of sem] by(auto simp add: has_sup_def)

      have "has_sup ((\<lambda>(f, y). f syn y) ` set (map (\<lambda>f. (f, sem)) (h1 # t1)))"
        using 1(2)[of "set (map (\<lambda> f . (f, sem))(h1#t1))" syn] 1(1) Sing unfolding Eq1 Eq2
        by(auto)

      then obtain s where S: "is_sup ((\<lambda>(f, y). f syn y) ` set (map (\<lambda>f. (f, sem)) (h1 # t1))) s"
        by(auto simp add: has_sup_def)

      have Union : "is_sup ({h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1) s" using S unfolding Eq3
        by auto

      show ?thesis using sup_union2[OF HSup Sup Union]
        by(auto simp add: has_sup_def)
    qed

    then obtain s' where S' : "is_sup {h1 syn sem, pcomps' t1 syn sem} s'"
      by(auto simp add: has_sup_def)

    have Conc'' : "is_sup {h1 syn sem, pcomps' t1 syn sem} [^ h1 syn sem, pcomps' (h2 # t2) syn sem ^]"
      using bsup_sup[OF S' bsup_spec] unfolding Cons'  by auto

    have Eqn :
  "(insert (h2 syn sem) (insert (h1 syn sem) ((\<lambda>x. x syn sem) ` set t2))) = 
   (insert (h1 syn sem) (insert (h2 syn sem) ((\<lambda>x. x syn sem) ` set t2)))"
      by auto

    show ?thesis 
      using sup_union1[OF HSup Sup Conc'']
      by(auto simp add: Cons' Eqn)
qed
*)

(*
lemma sups_pres_has_sup_pcomps' :
  assumes Hp : "sups_pres S"
  assumes H1 : "set l1 \<subseteq> S"
  assumes H2 : "set l2 \<subseteq> S"
  shows "has_sup {pcomps' l1, pcomps' l2}"
*)

(* TODO: are these later lemmas necessary? *)
(*
lemma sups_pres_tl_pcomps'_sup :
  assumes Hp : "sups_pres (set (h1#h2#h3#l))"
  shows "has_sup {h1 syn state, h2 syn state,  (pcomps' (h3#l)) syn state}" using assms
proof(induction l arbitrary: h1 h2 h3 syn state)
  case Nil
  then show ?case
  proof(cases rule: sups_pres.cases)
    case 1

    have S : "has_sup {state}"
      using sup_singleton[of state]
      by(auto simp add: has_sup_def)

    show ?thesis using 1[of "{(h1, state), (h2, state), (h3, state)}", of syn] Nil S
      by(auto)
  qed
next
  case (Cons h4 l)
  then show ?case 
    apply(auto)
qed
  case (1 Fs)
  then show ?case 
qed

(* sups_pres h t *)

lemma pcomps'_unique :
  assumes Hp : "sups_pres (set t)"
  assumes H : "x \<in> set t"
  shows "pcomps' (x#t) = pcomps' t" using assms
proof(induction t arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a1 t1)
  then show ?case 
  proof(cases "x = a1")
    case True
    show ?thesis unfolding True using pcomps'_cons_same[of a1 t1] by auto
  next
    case False
    then have Xin : "x \<in> set t1" using Cons.prems by auto

    have Fin : "finite (set (a1 # t1))" by blast

    have T1_pres : "sups_pres (set t1)" using Cons.prems
        sups_pres_subset[OF Cons.prems(1) Fin _ Xin] by auto

    show ?thesis 
    proof(cases t1)
      case Nil' : Nil

      then show ?thesis using Cons.prems by(simp add: bsup_idem)
    next
      case Cons' : (Cons a2 t2)
      show ?thesis 
      proof(rule ext; rule ext)
        fix syn state

        have SPa1a2 : "sups_pres {x, a1}"
          using sups_pres_subset[OF Cons.prems(1), of "{x, a1}"] using Cons.prems(2) Cons'
          by(auto)

        hence Supa1a2 : "has_sup {x syn state, a1 syn state}"
          using sups_pres_pair[OF SPa1a2] by auto

        have Eq0 : "{x syn state, a1 syn state, pcomps' (a2 # t2) syn state} =
                    {a1 syn state, x syn state, pcomps' (a2 # t2) syn state}" by auto

        have Sup3 : "has_sup {x syn state, a1 syn state, pcomps' (a2 # t2) syn state}" 
          using Cons.prems Cons' False apply(simp)

        hence Sup3' : "has_sup {a1 syn state, x syn state, pcomps' (a2 # t2) syn state}" 
          unfolding Eq0 by auto

        have Eq1 : "[^ x syn state, [^ a1 syn state, pcomps' (a2 # t2) syn state ^] ^] =
                    [^ [^ x syn state, a1 syn state ^], pcomps' (a2 # t2) syn state ^]"
          using bsup_assoc3[OF Sup3] by auto

        have Eq2 : "[^ [^ x syn state, a1 syn state ^], pcomps' (a2 # t2) syn state ^] =
                    [^ [^ a1 syn state, x syn state ^], pcomps' (a2 # t2) syn state ^]"
          using bsup_comm[OF Supa1a2] by auto

        have Eq3 : "[^ [^ a1 syn state, x syn state ^], pcomps' (a2 # t2) syn state ^] =
                    [^ a1 syn state, [^ x syn state , pcomps' (a2 # t2) syn state ^] ^]"
          unfolding sym[OF bsup_assoc3[OF Sup3']] by auto

        show "pcomps' (x # a1 # t1) syn state = pcomps' (a1 # t1) syn state"
          using fun_cong[OF fun_cong[OF Cons.IH[OF T1_pres Xin], of syn], of state] 
            Cons' Cons.prems
            Eq1 Eq2 Eq3
          by(auto)

      using Cons.IH[OF T1_pres Xin] Cons'
        apply(simp)


        have "[^ x syn state, pcomps' (a2 # t2) syn state ^] = pcomps' (a2 # t2) syn state"
          using fun_cong[OF fun_cong[OF Cons.IH[OF T1_pres Xin], of syn], of state] Cons'
          by(simp)

        hence "[^ x syn state, [^ x syn state, pcomps' (a2 # t2) syn state ^] ^] = 
               [^ x syn state, pcomps' (a2 # t2) syn state ^]" by simp

        

        show "pcomps' (x # a1 # t1) syn state = pcomps' (a1 # t1) syn state"

      using Cons.IH[OF T1_pres Xin] Cons'
        apply(simp)
        
    qed

      using Cons.IH[OF T1_pres Xin]
      apply(simp)

      sorry
  qed
qed


(* NB: this handles commutativity.
   what about associativity? 

need analogue of thing for sups where we show we can replace a set
with its sup when calculating sups
*)

(*

lemma sups_pres_assoc :
  fix S' 
  assume S' = pcomps ` l
  assume set L = S'
  shows pcomps L = pcomps (concat ...)


*)

lemma pcomps_cons :
  assumes H1 : "pcomps l1 = pcomps l2"
  shows "pcomps (a1 # l1) = pcomps (a1 # l2)" using assms
proof(induction l1 arbitrary: a1 l2)
  case Nil
  show ?case
  proof(cases l2)
    case Nil' : Nil
    then show ?thesis by auto
  next
    case Cons' : (Cons h2 t2)

(*
    show ?thesis
    proof(rule ext; rule ext)
      fix syn state
      have State : "state = pcomps (h2 # t2) syn state"
        using fun_cong[OF fun_cong[OF Nil, of syn], of state] Cons' 
        by(auto)

      show "pcomps [a1] syn state = pcomps (a1 # l2) syn state"
        using fun_cong[OF fun_cong[OF Nil, of syn], of state] Cons' 
        apply(auto)
      apply(auto)
*)
(* not convinced we need this case split. *)
    show ?thesis
    proof(cases t2)
      case Nil'' : Nil

      (* i think this is false.
         we need to explicitly rule out l1/l2 = [] *)
(*
      have "h2 = (\<lambda> a b . b)"
      proof(rule ext; rule ext)
        fix syn state

        have F : "(\<lambda>a b. b) = (\<lambda>a b. [^ h2 a b, b ^])" using Nil Cons' Nil''
        by(auto)

      show "h2 syn state = state" using 
          fun_cong[OF fun_cong[OF F, of syn], of state]
        apply(auto)
*)
      show ?thesis
      proof(rule ext; rule ext)
        fix syn state

        have Hh2 : "[^ h2 syn state, state ^] = state"
          using fun_cong[OF fun_cong[OF Nil, of syn], of state] Nil'' Cons' by auto

        hence "[^ a1 syn state, state ^] = [^ a1 syn state, [^ h2 syn state, state ^] ^]" 
          by auto

        hence "[^ a1 syn state, state ^] = [^ [^a1 syn state,  h2 syn state^], [^h2 syn state, state ^] ^]"
          using bsup_assoc_fact1 by auto

        hence "[^ a1 syn state, state ^] = [^ [^a1 syn state,  h2 syn state^], state ^]"
          unfolding Hh2 by auto

        thus "pcomps [a1] syn state = pcomps (a1 # l2) syn state" using Nil Nil'' Cons'
          by(auto)
      qed
    next
      case Cons'' : (Cons h3 t3)

      show ?thesis
      proof(rule ext; rule ext)
        fix syn state

        have "pcomps (h2 # h3 # t3) syn state = state"
          using fun_cong[OF fun_cong[OF Nil, of syn], of state]  Cons'' Cons' by(auto)

(*
        hence "[^ a1 syn state, state ^] = [^ a1 syn state, [^ h2 syn state, state ^] ^]" 
          by auto

        hence "[^ a1 syn state, state ^] = [^ [^a1 syn state,  h2 syn state^], [^h2 syn state, state ^] ^]"
          using bsup_assoc_fact1 by auto

        hence "[^ a1 syn state, state ^] = [^ [^a1 syn state,  h2 syn state^], state ^]"
          unfolding Hh2 by auto
*)
        thus "pcomps [a1] syn state = pcomps (a1 # l2) syn state" using Nil Cons'' Cons'
          by(auto simp add: bsup_arg_eq)
      qed
    qed
  qed
next
  case (Cons h1 t1)

  show ?case
  proof(cases l2)
    case Nil' : Nil
    then show ?thesis using Cons.prems apply( auto)
  next
    case Cons' : (Cons h2 t2)


  show ?case using Cons.prems apply(auto)
    qed
    

    have h2id :
    "h2 = (\<lambda> a b . b)"
      using Nil apply(cases t2; auto)

    then show ?thesis using Nil apply(cases t2; auto)
  qed

next
  case (Cons a l1)
  then show ?case sorry
qed

lemma sups_pres_pcomps' :
  assumes H : "sups_pres Fs"
  assumes Hl1 : "set l1 = Fs"
  assumes Hl2 : "set l2 = Fs"
  shows "pcomps l1 = pcomps l2" using H Hl1 Hl2
proof(induction l1 arbitrary: l2 Fs)
  case Nil
  then show ?case by auto
next
  case (Cons a1 l1)

  (* we know a1 \<in> l2 *)

  then have L2in : "a1 \<in> set l2" by auto

  hence Rew2 : "pcomps l2 = pcomps (a1 # l2)" 
    using pcomps_unique[of l2 a1] Cons.prems by auto

  show ?case
  proof(cases "a1 \<in> set l1")
    case True

    then have Set1 : "set l1 = Fs" using Cons.prems by auto

    hence Rew1 : "pcomps l1 = pcomps (a1 # l1)" 
      using pcomps_unique[of l1 a1] Cons.prems True unfolding Set1 by(auto)

    then show ?thesis unfolding sym[OF Rew1]
      using Cons.IH[OF _ Set1] Cons.prems by(auto)
  next
    case False

    (* idea: we are removing all a1 from l2, and then adding one back at the beginning *)

    then show ?thesis using Cons
  qed
    


  show ?case
  proof(cases l1)
    case Nil' : Nil
    then show ?thesis using Cons sorry
(* idea: l2 consists of only a1's. so pcomps l2 = pcomps [a1], qed *)
  next
    case Cons' : (Cons a2 l1')
    then show ?thesis
    proof(cases "a1 = a2")
      case True

      have Set' : "set (l1) = Fs"
        using Cons' True Cons.prems by(auto)

      have Conc' : "pcomps l1 = pcomps l2"
        using Cons' Cons.prems Cons.IH[OF Cons.prems(1) Set' Cons.prems(3)] 
        by(auto)

      thus ?thesis unfolding Cons' True sorry (* pcomps_unique *)
    next
      case False
      then show ?thesis using Cons Cons'
    qed
      apply(simp)
  qed

  hence Fin : "finite Fs" by auto

  have Pres' : "sups_pres (set l1)"
    using sups_pres_subset[OF Cons.prems(1) Fin]

  then show ?case using Cons
    
qed
  case empty
  then show ?case
    by(auto)
next
  case (insert x F)
  then show ?case 
    (* split on l1/l2 *)
    (* sups_pres (S1 \<union> S2) \<Longrightarrow> sups_pres S1 *)
qed
  case (1 Fs)
  then show ?case 
    apply(auto)
qed


(* generalize? subset? *)
lemma sups_pres_pcomps' :
  assumes Hfin : "finite Fs"
  assumes H : "sups_pres Fs"
  assumes Hl1 : "set l1 = Fs"
  assumes Hl2 : "set l2 = Fs"
  shows "pcomps l1 = pcomps l2" using Hfin H Hl1 Hl2
proof(induction Fs arbitrary: l1 l2)
  case empty
  then show ?case
    by(auto)
next
  case (insert x F)
  then show ?case 
    (* split on l1/l2 *)
    (* sups_pres (S1 \<union> S2) \<Longrightarrow> sups_pres S1 *)
qed
  case (1 Fs)
  then show ?case 
    apply(auto)
qed


(* how to express validity for multiple languages?
   one idea: validity predicate over a set of languages - that arbitrary subsets
   are lc_valid (?)
*)

inductive lc_valids :: "(('a \<Rightarrow> 'b :: Mergeable \<Rightarrow> 'b) set) \<Rightarrow> bool" where
"lc_valids {}"
| "\<And> f . lc_valids {f}"
(* | "\<And> f1 f2 . lc_valid (f1, f2) \<Longrightarrow> lc_valids {f1, f2}" *)
| "\<And> S f . lc_valids S \<Longrightarrow>
           (\<And> g . g \<in> S \<Longrightarrow> lc_valid (f, g)) \<Longrightarrow>
           lc_valids (insert f S)"

(* we want a notion of lc_valid for langcomps. *)
(* correctness: any permutation and assocation of pcomp will work. *)

lemma lc_valid_comp3 :
  fixes sem1 sem2 sem3 :: "('a \<Rightarrow> 'b :: Mergeable \<Rightarrow> 'b)"
  assumes H12 : "lc_valid (sem1, sem2)"
  assumes H23 : "lc_valid (sem2, sem3)"
  assumes H13 : "lc_valid (sem1, sem3)"
  shows "lc_valid ((pcomp (sem1, sem2)), sem3)"
proof(rule lc_valid_intro)
  fix syn 
  fix st1 st2 :: 'b
  assume "has_sup {st1, st2}"
  show "has_sup {Sem1 (pcomp (sem1, sem2), sem3) syn st1, Sem2 (pcomp (sem1, sem2), sem3) syn st2}"
    unfolding has_sup_def
    apply(simp)
    
(*
lemma lc_valid_lift :
  assumes Hlc : "lc = \<lparr> Sem1 = (l_map_s ls1 l1 f1)
                      , Sem2 = (l_map_s ls2 l2 f2) \<rparr>" 
  assumes Hsl : "sup_l ls1 ls2 l1 l2"
  shows "lc_valid lc"
proof(-)
  have "sup_pres
    (l_map_s ls1 l1 f1)
    (l_map_s ls2 l2 f2)" using sup_l_pres[OF Hsl] by auto

  thus "lc_valid lc" by(auto simp add:Hlc lc_valid_def)
qed
*)
*)

(*
lemma sup_l_comm :
  fixes ls1 :: "('x \<Rightarrow> 'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1  :: "('x1, 'a1, 'b :: Mergeableb, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Mergeableb, 'z2) lifting_scheme"
  assumes H : "sup_l ls1 ls2 l1 l2"
  shows "sup_l ls2 ls1 l2 l1"
proof(rule sup_lI)
  fix s :: "'x"
  fix a2 :: 'a2
  fix a1 :: "'a1"
  have "{LBase l2 (ls2 s), LBase l1 (ls1 s)} = {LBase l1 (ls1 s) , LBase l2 (ls2 s) }" by auto
  thus "has_sup {LBase l2 (ls2 s), LBase l1 (ls1 s)}" using sup_lDB[OF H, of s] by auto
next
  fix s :: "'x"
  fix a2 :: 'a2
  fix a1 :: 'a1
  fix b1 b2 :: 'b
  assume Hs : "has_sup {b1, b2}"

  have "{b2, b1} = {b1, b2}" by auto
  hence Hs' : "has_sup {b2, b1}" using Hs by auto
  have "{LUpd l1 (ls1 s) a1 b2, LUpd l2 (ls2 s) a2 b1} = {LUpd l2 (ls2 s) a2 b1, LUpd l1 (ls1 s) a1 b2}" by auto

  thus "has_sup {LUpd l2 (ls2 s) a2 b1, LUpd l1 (ls1 s) a1 b2}"
    using sup_lDI[OF H Hs', of s a1 a2] by auto
qed
*)
(* what might we want to show here?
- pairwise sup_l implies entire composition is well formed?
- something about associativity?
*)

(*
lemma sup_l_assoc :
  fixes ls1 :: "('x \<Rightarrow> 'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes ls3 :: "('x \<Rightarrow> 'x3)"
  fixes l1  :: "('x1, 'a1, 'b :: Mergeableb, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Mergeableb, 'z2) lifting_scheme"
  fixes l3 :: "('x3, 'a3, 'b :: Mergeableb, 'z3) lifting_scheme"
  assumes H : "sup_l ls1 ls2 l1 l2"
  shows "sup_l ls2 ls1 l2 l1"
proof(rule sup_lI)
*)
end