theory LangComp imports LiftUtils
begin

type_synonym ('a, 'b) langcomp =
  "('a \<Rightarrow> 'b \<Rightarrow> 'b) * ('a \<Rightarrow> 'b \<Rightarrow> 'b)"

abbreviation Sem1 ::
  "('a, 'b) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"Sem1 \<equiv> fst"

abbreviation Sem2 ::
  "('a, 'b) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"Sem2 \<equiv> snd"

(* TODO: need to show that this formulation works
   in the sense that if all semantics have LUBs in
   pairwise (?) fashion, then this is equivalent to
   any ordering of langcomp's *)
type_synonym ('a, 'b) langcomps =
  "('a \<Rightarrow> 'b \<Rightarrow> 'b) list"

(* idea: commutativity should mean that the ordering of composition doesn't matter *)
fun pcomps :: "('a, 'b :: Mergeable) langcomps \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomps [] a b = b"
| "pcomps [lh] a b = lh a b"
| "pcomps (lh#lt) a b =
   [^ [^ lh a b, pcomps lt a b ^], b ^]"

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
proof(rule is_ub_intro)
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
proof(rule is_sup_intro)
  fix x
  assume Hx : "x \<in> S1 \<union> S2"
  consider (1) "x \<in> S1" |
           (2) "x \<in> S2" using Hx by auto
  then show "x <[ x'"
  proof cases
    case 1
    then show ?thesis using is_sup_unfold1[OF Hsup1 1] is_sup_unfold1[OF HsupU, of x1]
      by(auto simp add: leq_trans[of x x1])
  next
    case 2
    then show ?thesis using is_sup_unfold1[OF Hsup2 2] is_sup_unfold1[OF HsupU, of x2]
      by(auto simp add: leq_trans[of x x2])
  qed
next
  fix x'a
  assume Hx'a : "is_ub (S1 \<union> S2) x'a"

  have "is_ub S1 x'a" using Hx'a
    by(auto simp add: is_ub_def)

  hence Ub1: "x1 <[ x'a"
    using is_sup_unfold2[OF Hsup1] by auto

  have "is_ub S2 x'a" using Hx'a
    by(auto simp add: is_ub_def)

  hence Ub2: "x2 <[ x'a"
    using is_sup_unfold2[OF Hsup2] by auto

  have "is_ub {x1, x2} x'a" using Ub1 Ub2
    by(auto simp add: is_ub_def)

  thus "x' <[ x'a"
    using is_sup_unfold2[OF HsupU] by auto
qed


lemma ub_union2 :
  assumes Hsup1 : "is_sup S1 x1"
  assumes Hsup2 : "is_sup S2 x2" 
  assumes HsupU : "is_ub (S1 \<union> S2) x'"
  shows HsupU : "is_ub {x1, x2} x'"
proof(rule is_ub_intro)
  fix x

  assume Hx : "x \<in> {x1, x2}"

  then consider (1) "x = x1" | (2) "x = x2"
    by auto

  then show "x <[ x'"
  proof cases
    case 1
    have "is_ub S1 x'"
      using HsupU by(auto simp add: is_ub_def)
    thus ?thesis using is_sup_unfold2[OF Hsup1] 1 by auto
  next
    case 2
    have "is_ub S2 x'"
      using HsupU by(auto simp add: is_ub_def)
    thus ?thesis using is_sup_unfold2[OF Hsup2] 2 by auto
  qed
qed

lemma sup_union2 :
  assumes Hsup1 : "is_sup S1 x1"
  assumes Hsup2 : "is_sup S2 x2"
  assumes HsupU : "is_sup (S1 \<union> S2) x'"
  shows "is_sup {x1, x2} x'" 
proof(rule is_sup_intro)
  fix x
  assume Hx : "x \<in> {x1, x2}"

  then consider (1) "x = x1" | (2) "x = x2"
    by auto

  then show "x <[ x'"
  proof cases
    case 1
    have "is_ub S1 x'"
      using is_sup_unfold1[OF HsupU] by(auto simp add: is_ub_def)
    thus ?thesis using is_sup_unfold2[OF Hsup1] 1 by auto
  next
    case 2
    have "is_ub S2 x'"
      using is_sup_unfold1[OF HsupU] by(auto simp add: is_ub_def)
    thus ?thesis using is_sup_unfold2[OF Hsup2] 2 by auto
  qed
next
  fix x'a
  assume Hx'a : "is_ub {x1, x2} x'a"

  have "is_ub (S1 \<union> S2) x'a"
  proof(rule is_ub_intro)
    fix x
    assume Hx : "x \<in> S1 \<union> S2"
    then consider (1) "x \<in> S1" | (2) "x \<in> S2" by auto
    then show "x <[ x'a"
    proof cases
      case 1
      hence Leq1 : "x <[ x1" using is_sup_unfold1[OF Hsup1] by auto
      have Leq2 : "x1 <[ x'a" using Hx'a by(auto simp add: is_ub_def)
      show ?thesis
        using leq_trans[OF Leq1 Leq2] by auto
    next
      case 2
      hence Leq1 : "x <[ x2" using is_sup_unfold1[OF Hsup2] by auto
      have Leq2 : "x2 <[ x'a" using Hx'a by(auto simp add: is_ub_def)
      show ?thesis
        using leq_trans[OF Leq1 Leq2] by auto
    qed
  qed

  thus "x' <[ x'a"
    using is_sup_unfold2[OF HsupU] by auto
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
(* ok, so the idea is now we convert our sup premise to a union
 then we can get existence of a sup for pair of sups
then go back *)
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