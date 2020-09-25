theory LangComp imports LiftUtils
begin

record ('a, 'b) langcomp =
  Sem1 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  Sem2 :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

(* TODO: need to show that this formulation works
   in the sense that if all semantics have LUBs in
   pairwise (?) fashion, then this is equivalent to
   any ordering of langcomp's *)
type_synonym ('a, 'b) langcomps =
  "('a \<Rightarrow> 'b \<Rightarrow> 'b) list"

fun pcomps :: "('a, 'b :: Mergeable) langcomps \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomps [] a b = b"
| "pcomps [lh] a b = lh a b"
| "pcomps (lh#lt) a b =
   [^ [^ lh a b, pcomps lt a b ^], b ^]"

(*
fun pcomps' :: "('a \<Rightarrow> 'b \<Rightarrow> 'b)  \<Rightarrow> ('a, 'b :: Mergeable) langcomps \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomps' lh a b = lh a b"
| "pcomps' (lh1) [lh2] a b =
   [^ [^ lh a b, 
*)
(* idea:
   - get 
*)
(*
definition pcomp' :: "('a, 'b :: Mergeable) langcomp \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomp' l a b =
  [^ [^ Sem2 l a b, Sem1 l a b ^], b ^]"
*)

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
   ('x1, 'a1, ('b :: Pord), 'z1) lifting_scheme \<Rightarrow>
   ('x2, 'a2, ('b :: Pord), 'z2) lifting_scheme \<Rightarrow>
   bool" where
"sup_l ls1 ls2 l1 l2 =
  (\<forall> s a1 a2 b1 b2 .
    has_sup {LNew l1 (ls1 s) a1, LNew l2 (ls2 s) a2} \<and>
    (has_sup {b1, b2} \<longrightarrow> has_sup {LUpd l1 (ls1 s) a1 b1, LUpd l2 (ls2 s) a2 b2}) \<and>
    (has_sup {b1, b2} \<longrightarrow> has_sup {LPost l1 (ls1 s) b1, LPost l2 (ls2 s) b2}))"

lemma sup_l_intro :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Pord, 'z2) lifting_scheme"
  assumes H1 : "\<And> s a1 a2 . has_sup {LNew l1 (ls1 s) a1, LNew l2 (ls2 s) a2}"
  assumes H2 : "\<And> s a1 a2 b1 b2 . has_sup {b1, b2} \<Longrightarrow> has_sup {LUpd l1 (ls1 s) a1 b1, LUpd l2 (ls2 s) a2 b2}"
  assumes H3 : "\<And> s b1 b2 . has_sup {b1, b2} \<Longrightarrow> has_sup {LPost l1 (ls1 s) b1, LPost l2 (ls2 s) b2}"
  shows "sup_l ls1 ls2 l1 l2" using H1 H2 H3
  by(auto simp add:sup_l_def)

lemma sup_l_unfold1 :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Pord, 'z2) lifting_scheme"
  assumes H : "sup_l ls1 ls2 l1 l2"  
  shows "has_sup {LNew l1 (ls1 s) a1, LNew l2 (ls2 s) a2}"
  using H   by(auto simp add:sup_l_def)

lemma sup_l_unfold2 :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Pord, 'z2) lifting_scheme"
  assumes Hs : "sup_l ls1 ls2 l1 l2"
  assumes Hb : "has_sup {b1, b2}"
  shows "has_sup {LUpd l1 (ls1 s) a1 b1, LUpd l2 (ls2 s) a2 b2}"
  using  Hb Hs
  by(auto simp add:sup_l_def)

lemma sup_l_unfold3 :
  fixes ls1 :: "('x \<Rightarrow>'x1)"
  fixes ls2 :: "('x \<Rightarrow> 'x2)"
  fixes l1 :: "('x1, 'a1, 'b :: Pord, 'z1) lifting_scheme"
  fixes l2 :: "('x2, 'a2, 'b :: Pord, 'z2) lifting_scheme"
  assumes Hs : "sup_l ls1 ls2 l1 l2"
  assumes Hb : "has_sup {b1, b2}"
  shows "has_sup {LPost l1 (ls1 s) b1, LPost l2 (ls2 s) b2}"
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
(*
lemma sup_l_pres :
  fixes ls1 :: "'syn \<Rightarrow> 'syn1"
  fixes ls2 :: "'syn \<Rightarrow> 'syn2"
  fixes l1 :: "('syn1, 'a1, 'b :: Mergeable, 'z1) lifting_scheme"
  fixes l2 :: "('syn2, 'a2, 'b :: Mergeable, 'z2) lifting_scheme"
  fixes f1 :: "'syn1 \<Rightarrow> 'a1 \<Rightarrow> 'a1"
  fixes f2 :: "'syn2 \<Rightarrow> 'a2 \<Rightarrow> 'a2"
  assumes Hsl : "sup_l ls1 ls2 l1 l2"
  shows "sup_pres
    (l_map_s ls1 l1 f1)
    (l_map_s ls2 l2 f2)"
proof(rule sup_pres_intro)
  fix syn :: 'syn
  fix st1 :: 'b
  fix st2 :: 'b
  assume Hsup : "has_sup {st1, st2}"
  show "has_sup {l_map_s ls1 l1 f1 syn st1, l_map_s ls2 l2 f2 syn st2}"

    using Hsup sup_l_unfold2[OF Hsl] sup_l_unfold3[OF Hsl]
    apply(auto simp add: l_map_s_def LNew_def split:option.splits)
qed
*)
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
proof(rule sup_l_intro)
  fix s :: "'x"
  fix a2 :: 'a2
  fix a1 :: "'a1"
  have "{LNew l2 (ls2 s) a2, LNew l1 (ls1 s) a1} = {LNew l1 (ls1 s) a1, LNew l2 (ls2 s) a2}" by auto
  thus "has_sup {LNew l2 (ls2 s) a2, LNew l1 (ls1 s) a1}" using sup_l_unfold1[OF H, of s a1 a2] by auto
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
    using sup_l_unfold2[OF H Hs', of s a1 a2] by auto
next
  fix s :: 'x
  fix b1 b2 :: 'b
  assume Hs : "has_sup {b1, b2}"

  have "{b2, b1} = {b1, b2}" by auto
  hence Hs' : "has_sup {b2, b1}" using Hs by auto
  have "{LPost l1 (ls1 s) b2, LPost l2 (ls2 s) b1} = {LPost l2 (ls2 s) b1, LPost l1 (ls1 s) b2}" by auto

  thus "has_sup {LPost l2 (ls2 s) b1, LPost l1 (ls1 s) b2}"
    using sup_l_unfold3[OF H Hs', of s] by auto
qed


end