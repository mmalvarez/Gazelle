theory Pord imports Main

begin

(* these may be useful primitives, but are not currently used *)
definition ord_leq :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"ord_leq o1 o2 = (\<forall> x1 x2 . o1 x1 x2 \<longrightarrow> o2 x1 x2)"

lemma ord_leq_refl : "\<And> ord . ord_leq ord ord"
  apply(simp add:ord_leq_def)
  done

lemma ord_leq_trans: "\<And> ox oy oz . ord_leq ox oy \<Longrightarrow> ord_leq oy oz \<Longrightarrow> ord_leq ox oz"
  apply(simp add:ord_leq_def)
  done

lemma ord_leq_antisym : "\<And> ox oy . ord_leq ox oy
 \<Longrightarrow> ord_leq oy ox \<Longrightarrow> ox = oy"
  apply(simp add:ord_leq_def)
  apply(blast)
  done

lemma ord_leq' : "\<And> ox oy a b .
  ord_leq ox oy \<Longrightarrow>
  ox a b \<Longrightarrow>
  oy a b"
  apply(simp add:ord_leq_def)
  done

lemma ord_leq_d : "\<And> ox oy a b .
  ox a b \<Longrightarrow>
  ord_leq ox oy \<Longrightarrow>
  oy a b"
  apply(simp add:ord_leq_def)
  done

class Pord_Weak =
  (* p stands for partial; used to distinguish from Isabelle's
     built in (overloaded) leq to ensure there is no ambiguity.
     TODO: figure out how to create typeclass instances when
     we instantiate this locale *)
  fixes pleq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl \<open><[\<close> 71)
  assumes
    leq_refl : "pleq a a"
  assumes
    leq_trans : "pleq a b \<Longrightarrow> pleq b c \<Longrightarrow> pleq a c"


(* helpful lemmas about Pord_Weak *)
definition is_lb :: "('a :: Pord_Weak) set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_lb A a =
  (\<forall> x \<in> A . a <[ x)"

definition is_greatest :: "(('a :: Pord_Weak) \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_greatest P a =
  (P a \<and>
   (\<forall> a' . P a' \<longrightarrow> pleq a' a))"

definition is_inf :: "('a :: Pord_Weak) set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_inf A a = is_greatest (is_lb A) a"

definition is_ub :: "('a :: Pord_Weak) set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_ub A a =
  (\<forall> x \<in> A . pleq x a)"

definition is_least :: "(('a :: Pord_Weak) \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
"is_least P a =
  (P a \<and>
   (\<forall> a' . P a' \<longrightarrow> pleq a a'))"

definition is_sup :: "('a :: Pord_Weak) set \<Rightarrow> 'a \<Rightarrow> bool" where
"is_sup A a =
  is_least (is_ub A) a"

definition has_sup :: "('a :: Pord_Weak) set \<Rightarrow> bool" where
"has_sup A = (\<exists> s . is_sup A s)"

definition has_ub :: "('a :: Pord_Weak) set \<Rightarrow> bool" where
"has_ub A = (\<exists> s . is_ub A s)"

definition is_bub :: "('a :: Pord_Weak) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bub a b s =
  (pleq a s \<and>
    ((\<forall> bd sd . pleq bd (b) \<longrightarrow>
                is_sup {a, bd} sd \<longrightarrow>
                pleq sd (s))))"

definition is_bsup :: "('a :: Pord_Weak) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"is_bsup a b s =
  is_least (is_bub a b) s"

(* monotonicity of predicates
   useful for reasoning about semantics  *)
definition is_monop1 :: "(('a :: Pord_Weak) \<Rightarrow> bool) \<Rightarrow> bool" where
"is_monop1 P =
  (\<forall> a b . pleq a b \<longrightarrow> P a \<longrightarrow> P b)"

definition is_monop2 :: "(('a :: Pord_Weak) \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"is_monop2 P =
  (\<forall> a1 b1 a2 b2 .
    pleq a1 b1 \<longrightarrow>
    pleq a2 b2 \<longrightarrow>
    P a1 a2 \<longrightarrow>
    P b1 b2)"

(* "contravariant" version *)
definition is_monop2' :: "(('a :: Pord_Weak) \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"is_monop2' P =
  (\<forall> a1 b1 a2 b2 .
    pleq a1 b1 \<longrightarrow>
    pleq b2 a2 \<longrightarrow>
    P a1 a2 \<longrightarrow>
    P b1 b2)"

(* monotonicity for functions *)
definition is_mono :: "(('a :: Pord_Weak) \<Rightarrow> 'a) \<Rightarrow> bool" where
"is_mono f =
  (\<forall> a b .
     pleq a b \<longrightarrow>
     pleq (f a) (f b))"

(* convenience lemmas, true by definition *)
lemma is_ub_intro :
  assumes H : "\<And> x . x \<in> A \<Longrightarrow> pleq x a"
  shows "is_ub A a" using H
  by(auto simp add:is_ub_def)

lemma is_ub_unfold :
  assumes H1 : "is_ub S ub"
  assumes H2 : "x \<in> S"
  shows "pleq x ub"
  using H1 H2
  by (auto simp add: is_ub_def)

lemma is_sup_intro :
  assumes Hpleq : "\<And> x . x \<in> A \<Longrightarrow> pleq x ub"
  assumes Hleast : "\<And> x' . is_ub A x' \<Longrightarrow> pleq ub x'"
  shows "is_sup A ub" using Hpleq Hleast
  by(auto simp add:is_least_def is_ub_def is_sup_def)

lemma is_sup_unfold1 :
  assumes H1 : "is_sup S ub"
  assumes H2 : "x \<in> S"
  shows "pleq x ub"
  using H1 H2
  by (auto simp add: is_ub_def is_least_def is_sup_def)

lemma is_sup_unfold2 :
  assumes H1 : "is_sup S ub"
  assumes H2 : "is_ub S ub'"
  shows "pleq ub ub'"
  using H1 H2
  by (auto simp add: is_ub_def is_least_def is_sup_def)

lemma bsup_leq :
  assumes H : "is_bsup a b x"
  shows "pleq a x" using H
  by (auto simp add:is_bsup_def is_bub_def is_least_def)


lemma is_bub_unfold1 :
  assumes H1 : "is_bub a b ub"
  shows "pleq a ub" 
  using H1 by (auto simp add:is_bub_def)

lemma is_bub_unfold2 :
  assumes H1 : "is_bub a b ub"
  assumes H2 : "pleq bd (b)"
  assumes H3 : "is_sup {a, bd} sd"
  shows "pleq sd (ub)"
  using H1 H2 H3 by (auto simp add:is_bub_def)

lemma is_bsup_intro :
  assumes Hpleq : "pleq a bub"
  assumes Hbub :
    "\<And> bd sd . pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd bub"
  assumes Hleast : "\<And> x' . is_bub a b x' \<Longrightarrow> pleq bub x'"
  shows "is_bsup a b bub" using Hpleq Hbub Hleast
  by(auto simp add:is_bsup_def is_least_def is_bub_def)

lemma is_bsup_unfold1 :
  assumes H1 : "is_bsup a b ub"
  shows "pleq a ub" 
  using H1 by (rule bsup_leq)

lemma is_bsup_unfold2 :
  assumes H1 : "is_bsup a b ub"
  assumes H2 : "pleq bd (b)"
  assumes H3 : "is_sup {a, bd} sd"
  shows "pleq sd (ub)"
  using H1 H2 H3 by (auto simp add:is_bub_def is_bsup_def is_least_def)

lemma is_bsup_unfold3 :
  assumes H1 : "is_bsup a b ub"
  assumes H2 : "is_bub a b ub'"
  shows "pleq ub ub'"
  using H1 H2 by (auto simp add:is_bsup_def is_least_def)

class Pord =
    Pord_Weak +
    assumes leq_antisym : "pleq a b \<Longrightarrow> pleq b a \<Longrightarrow> a = b"


(* facts about Pord *)
lemma is_greatest_unique :
  fixes P :: "('a :: Pord) \<Rightarrow> bool"
  fixes a b :: "('a :: Pord)"
  assumes H1 : "is_greatest P a"
  assumes H2 : "is_greatest P b"
  shows "a = b"
proof(-)
  have 0 :  "a <[ b" using H2 H1
    by(auto simp add:is_greatest_def)
  have 1 : "b <[ a" using H1 H2
    by(auto simp add:is_greatest_def)

  thus "a = b" using 0 1 by (auto intro: leq_antisym)
qed

lemma is_least_unique :
  fixes P :: "('a :: Pord) \<Rightarrow> bool"
  fixes a b :: "('a :: Pord)"
  assumes H1 : "is_least P a"
  assumes H2 : "is_least P b"
  shows "a = b"
proof(-)
  have 0 :  "a <[ b" using H2 H1
    by(auto simp add:is_least_def)
  have 1 : "b <[ a" using H1 H2
    by(auto simp add:is_least_def)

  thus "a = b" using 0 1 by (auto intro: leq_antisym)
qed

(* facts about sup *)

lemma is_sup_unique :
  fixes P :: "('a :: Pord) set"
  fixes x y :: "'a"
  shows "is_sup P x \<Longrightarrow> is_sup P y \<Longrightarrow> x = y"
proof(auto simp add:is_sup_def is_least_unique)
qed

lemma is_sup_comm2 :
  "is_sup {a, b} x \<Longrightarrow> is_sup {b, a} x"
proof(auto simp add:is_sup_def is_least_def is_ub_def)
qed

lemma sup_extend :
  assumes Hleq : "pleq a x"
  assumes Hlub1 : "is_sup {a, c} u1"
  assumes Hlub2 : "is_sup {x, c} u2"
  shows "pleq u1 u2"
proof(-)
  have 0 :  "pleq x u2" using Hlub2 by (auto simp add:is_sup_def is_ub_def is_least_def)
  have 1 :  "pleq a u2" using leq_trans[OF Hleq 0] by auto
  hence "is_ub {a, c} u2" using Hlub2
    by (auto simp add:is_sup_def is_ub_def is_least_def)

  thus ?thesis using Hlub1
    by (auto simp add:is_sup_def is_ub_def is_least_def)
qed

(* facts about bsup *)

lemma bsup_unique : 
  fixes a b x :: "'a :: Pord"
  assumes H1 : "is_bsup a b x"
  assumes H2 : "is_bsup a b x'"
  shows "x = x'"
  using H1 H2
proof(-)
  have 0 : "is_bub a b x'" using H2
    by(auto simp add:is_bsup_def is_least_def)

  have 1 : "pleq x x'" using 0 H1
    by(auto simp add:is_bsup_def is_least_def)

  have 2 : "is_bub a b x" using H1
    by(auto simp add:is_bsup_def is_least_def)

  have 3 : "pleq x' x" using 2 H2
    by(auto simp add:is_bsup_def is_least_def)

  show ?thesis using leq_antisym 1 3 by auto
qed


class Pordc =
  Pord +
  assumes complete2: "has_ub {a, b} \<Longrightarrow> has_sup {a, b}"

lemma is_bub_intro :
  assumes Hpleq : "pleq a bub"
  assumes Hbub :
    "\<And> bd sd . pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd bub"
  shows "is_bub a b bub" using Hpleq Hbub
  by(auto simp add:is_bub_def)


lemma bsup_compare1:
  fixes a b bs_ab a' b' bs_a'b :: "'a :: Pordc"
  assumes Hbsup1 : "is_bsup a b bs_ab"
  assumes Hbsup2 : "is_bsup a' b' bs_a'b'"
  assumes Hleqa : "pleq a a'"
  assumes Hleqa' : "pleq a' bs_ab"
  assumes Hdesc : "\<And> bd sd . pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> 
                        (pleq bd (b'))" (* can we get away with has_ub here? *)
  shows "pleq (bs_ab) (bs_a'b')"
proof(-)
  have Bub : "is_bub a b bs_a'b'"
  proof(-)

    have Hbub : "\<And> bd sd . pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd (bs_ab)" using Hbsup1
      by(auto simp add:is_bsup_def is_bub_def is_least_def) 
    
    have Hbub' : "\<And> bd sd . pleq bd (b') \<Longrightarrow> is_sup {a', bd} sd \<Longrightarrow> pleq sd (bs_a'b')" using Hbsup2
      by(auto simp add:is_bsup_def is_bub_def is_least_def) 

    have Conc1 : "pleq a (bs_a'b')" using Hleqa
    proof(-)
      have in0 : "pleq a' (bs_a'b')" using bsup_leq Hbsup2 by auto
      thus ?thesis using leq_trans[OF Hleqa in0] by auto
    qed

    have Conc2 : "\<And> bd sd . pleq bd (b) \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd (bs_a'b')"
    proof(-)
      fix bd sd
      assume Hbd : "pleq bd (b)"
      assume Hsup : "is_sup {a, bd} sd"

      have 0 : "pleq bd (b')" using Hdesc[OF Hbd Hsup] by auto
(*      have 1 : "pleq bd (aug (bsup a' b'))" using Hdesc[OF Hbd Hsup] *)

      have 1 : "pleq bd sd" using Hsup 
        by(auto simp add: is_sup_def is_ub_def is_least_def)

      have 2 : "pleq sd (bs_ab)" using Hbub[OF Hbd Hsup] by auto

      have "pleq bd (bs_ab)" using leq_trans[OF 1 2] by auto 

      hence 3 : "is_ub {(a'), bd} ((bs_ab))" using Hleqa'
        by(auto simp add:is_ub_def leq_refl) 

      hence 4 : "has_ub {(a'), bd}"
        by (auto simp add:has_ub_def)

      hence 5 : "has_sup {(a'), bd}"
        by (auto simp add:complete2)

      then obtain sd' where Hsd' : "is_sup {a', bd} sd'" by (auto simp add:has_sup_def)

      have 6: "pleq sd' (bs_a'b')" using Hbub'[OF 0 Hsd'] by auto

      have 8 : "pleq sd sd'" using sup_extend[OF Hleqa Hsup Hsd'] by auto
      
      show "pleq sd (bs_a'b')" using leq_trans[OF 8 6] by auto
    qed

    then show ?thesis using Conc1 Conc2 by(simp add:is_bub_def) 
  qed
  thus ?thesis using Hbsup1
    by(auto simp add:is_bsup_def is_least_def)
qed

(* do we really need to prove this again?
or can we do something more general? *)
lemma bsup_compare2:
  fixes a b bs_ab a' b' bs_a'b :: "'a :: Pordc"
  assumes Hbsup1 : "is_bsup a' b' bs_a'b'"
 assumes Hbsup2 : "is_bsup a b bs_ab"
 assumes Hleqa' : "pleq a' a"
 assumes Hleqa : "pleq a (bs_a'b')" 
(*  assumes Hleqb : "l_pleq b b'" *)
  assumes Hdesc : "\<And> bd sd . pleq bd (b) \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> 
                        (pleq bd (b'))" (* can we get away with has_ub here? *)
(* also used to have:  \<and> pleq bd (aug (bsup a' b')) *)
  shows "pleq bs_ab bs_a'b'"
proof(-)
  have Bub : "is_bub a b bs_a'b'"
  proof(-)

    have Hbub : "\<And> bd sd . pleq bd (b) \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd (bs_ab)" using Hbsup2
      by(auto simp add: is_bsup_def is_bub_def is_least_def) 
    
    have Hbub' : "\<And> bd sd . pleq bd (b') \<Longrightarrow> is_sup {a', bd} sd \<Longrightarrow> pleq sd bs_a'b'" using Hbsup1
      by(auto simp add: is_bsup_def is_bub_def is_least_def) 

    have Conc1 : "pleq a (bs_a'b')" using Hleqa by auto

    have Conc2 : "\<And> bd sd . pleq bd (b) \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd (bs_a'b')"
    proof(-)
      fix bd sd
      assume Hbd : "pleq bd (b)"
      assume Hsup : "is_sup {a, bd} sd"

      have 0 : "pleq bd (b')" using Hdesc[OF Hbd Hsup] by auto

      have 1 : "pleq bd sd" using Hsup 
        by(auto simp add: is_sup_def is_ub_def is_least_def)

      have 2 : "pleq sd (bs_ab)" using Hbub[OF Hbd Hsup] by auto

      have 3 : "pleq bd (bs_ab)" using leq_trans[OF 1 2] by auto 

      have 4 : "pleq a' (bs_ab)" using leq_trans[OF Hleqa' bsup_leq[OF Hbsup2]]
        by auto

      hence 5 : "is_ub {(a'), bd} (bs_ab)" using 3
        by(auto simp add:is_ub_def leq_refl)

      hence 6 : "has_ub {(a'), bd}" by (auto simp add:has_ub_def)

      have 7: "has_sup {a', bd}" using complete2[OF 6] by auto

      have 8 : "pleq bd (b')" using Hdesc[OF Hbd Hsup] by auto

      obtain sd' where Hsd' : "is_sup {a', bd} sd'" using 7 by (auto simp add:has_sup_def)

      have 9 : "pleq sd' (bs_a'b')" using Hbub'[OF 8 Hsd'] by auto

      have 10 : "pleq bd sd'" using Hsd' by (auto simp add:is_sup_def is_least_def is_ub_def)

      have 11 : "pleq bd (bs_a'b')" using leq_trans[OF 10 9] by auto

      have 12 : "is_ub {(a), bd} (bs_a'b')" using Hleqa 11
        by(auto simp add:is_ub_def)

      show "pleq sd (bs_a'b')" using 12 Hsup
        by(auto simp add:is_ub_def is_sup_def is_least_def)
    qed

    then show ?thesis using Conc1 Conc2 by(simp add:is_bub_def) 
  qed
  thus ?thesis using Hbsup2
    by(auto simp add:is_bsup_def is_least_def)
qed

lemma bsup_mono2 :
  fixes a b bs_ab a' b' bs_ab' :: "'a :: Pordc"
  assumes H: "pleq b b'"
  assumes Hbsup1 : "is_bsup a b bs_ab"
  assumes Hbsup2 : "is_bsup a b' bs_ab'"
  shows   "pleq (bs_ab) (bs_ab')"

proof(-)

  have Hbound :
     "(\<And>bd sd. pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq bd b') "
  proof(-)
    fix bd sd
    assume H1 : "pleq bd b"
    assume H2 : "is_sup {a, bd} sd"

    show "pleq bd b'" using leq_trans[OF H1 H] by auto
  qed
  
  show ?thesis using bsup_compare1[OF Hbsup1 Hbsup2 leq_refl[of a] bsup_leq[OF Hbsup1] Hbound] by auto
qed

lemma bsup_sup :
  fixes a b bs_ab :: "'a :: Pordc"
  assumes Hsup : "is_sup {a, b} s_ab" 
  assumes Hbsup : "is_bsup a b bs_ab"
  shows "is_sup {a, b} bs_ab"
proof(-)

  have Bub : "is_bub a b s_ab"
  proof(-)
    have Conc1 : "pleq a s_ab" using Hsup
      by(auto simp add:is_sup_def is_least_def is_ub_def)

    have Conc2 :
      "\<And> bd sd . pleq bd b \<Longrightarrow> is_sup {a, bd} sd \<Longrightarrow> pleq sd s_ab"
    proof(-)
      fix bd sd
      assume Hi1 : "pleq bd b"
      assume Hi2 : "is_sup {a, bd} sd"

      have 0 : "pleq bd sd"
        using Hi2 by (auto simp add:is_sup_def is_least_def is_ub_def)

      have 1 : "pleq b s_ab"
        using Hsup by (auto simp add:is_sup_def is_least_def is_ub_def)

      have 2 : "pleq bd s_ab"
        using leq_trans[OF Hi1 1] by auto

      have "is_ub {a, bd} s_ab" using Conc1 2
        by(auto simp add:is_ub_def)

      thus "pleq sd s_ab" using Hi2
        by(auto simp add:is_sup_def is_least_def)
    qed

    show ?thesis using Conc1 Conc2
      by (auto simp add: is_bub_def)
  qed

  have bs_ab_Lt : "pleq bs_ab s_ab" using Bub Hbsup
    by(auto simp add:is_bsup_def is_least_def)

  have Ub : "is_ub {a, b} bs_ab"
  proof(-)
    have Conc1 : "pleq a bs_ab" using Hbsup
      by(auto simp add:is_bsup_def is_bub_def is_least_def)

    have 0 : "pleq b s_ab" using Hsup by (auto simp add:is_sup_unfold1)

    have 1 : "pleq s_ab bs_ab" using is_bsup_unfold2[OF Hbsup leq_refl Hsup] by auto

    have Conc2 : "pleq b bs_ab" using leq_trans[OF 0 1] by auto

    show ?thesis using Conc1 Conc2 by
      (auto simp add:is_ub_def)
  qed

  have s_ab_Lt : "pleq s_ab bs_ab" using Ub Hsup
    by(auto simp add: is_sup_def is_least_def)

  show ?thesis using leq_antisym[OF bs_ab_Lt s_ab_Lt] Hsup by auto
qed


lemma leq_completion :
  fixes a a' b x :: "'a :: Pordc"
  assumes Hleq : "pleq a a'"
  assumes Hsup : "is_sup {a', b} x"

shows "has_sup {a, b}"
proof(-)
  have 0 :  "pleq a' x" using Hsup by (simp add:is_sup_def is_least_def is_ub_def)
  have 1 : "pleq a x" using leq_trans[OF Hleq 0] by auto
  hence 2 : "is_ub {a, b} x" using Hsup by (simp add:is_sup_def is_least_def is_ub_def)
  hence 3 : "has_ub {a, b}" by (auto simp add:has_ub_def)
  thus ?thesis by (auto elim: complete2)
qed


lemma bsup_imp_sup :
  assumes Hbs : "is_bsup a b bs"
  assumes H : "pleq b bs"
  shows "is_sup {a, b} bs"

proof(rule is_sup_intro)
  fix x
  assume Hx : "x \<in> {a, b}"
  show "pleq x bs" using H bsup_leq[OF Hbs] Hx
    by(auto)
next
  fix ub
  assume Hi :  "is_ub {a, b} ub"

  have 0 : "is_bub a b ub"
  proof(rule is_bub_intro)
    show "pleq a ub" using Hi by (auto simp add:is_ub_def)
  next
    fix bd sd
    assume Hl : "pleq bd b"
    assume Hs : "is_sup {a, bd} sd"

    have 0 : "is_ub {a, bd} ub" using Hi Hl leq_trans[of bd b ub]
      by(auto simp add:is_ub_def)

    show "pleq sd ub" using is_sup_unfold2[OF Hs 0] by auto
  qed

  show "pleq bs ub" using is_bsup_unfold3[OF Hbs 0] by auto
qed

lemma bsup_imp_sup_conv :
  fixes a b bs ub :: "'a :: Pordc"
  assumes Hbs : "is_bsup a b bs"
  assumes H : "\<not> pleq b bs"
  assumes Hub : "is_ub {a, b} ub"
  shows False
proof(-)
  obtain lub where Hlub : "is_sup {a, b} lub" using Hub complete2 by(auto simp add:has_ub_def has_sup_def)
  have Hbub : "is_bub a b bs" using Hbs by(auto simp add:is_bsup_def is_least_def)
  have "pleq lub bs" using is_bub_unfold2[OF Hbub leq_refl[of b] Hlub] by auto
  hence "pleq b bs" using Hlub leq_trans[of b lub bs] by (auto simp add:is_sup_def is_least_def is_ub_def)
  thus ?thesis using H by auto
qed

class Pordb =  Pord +
fixes bot :: "'a :: Pord_Weak" ("\<bottom>")
assumes bot_spec :
  "\<And> (a :: 'a ) .  pleq bot a"

class Pordbc =  Pordc + Pordb

end