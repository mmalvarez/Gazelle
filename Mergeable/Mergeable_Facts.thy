theory Mergeable_Facts imports Mergeable
begin

(* Assorted useful extra lemmas about Pord and Mergeable. 
 *)

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
(*
lemma ub_finite_all :
  fixes S :: "('b :: Pordc_all) set"
  fixes x :: "'b"
  assumes Hfin : "finite S"
  assumes Hx : "x \<in> S" 
  shows "\<exists> sub . is_ub S sub" using assms
proof(induction S arbitrary: x)
  case empty
  then show ?case 
    by auto
next
  case (insert x1 S')
  show ?case
  proof(cases "S' = {}")
    case True
    then have "is_ub (insert x1 S') x1"
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
*)

(*
lemma sup_finite_all :
  fixes S :: "('b :: Pordc_all) set"
  fixes x :: "'b"
  assumes Hfin : "finite S"
  assumes Hx : "x \<in> S" 
  shows "\<exists> ssup . is_sup S ssup" using assms
proof(induction S arbitrary: x)
  case empty
  then show ?case 
    by auto
next
  case (insert x1 S')
  show ?case
  proof(cases "S' = {}")
    case True
    then have "is_ub (insert x1 S') x1"
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

*)

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

lemma bsup_base_leq2 :
  assumes H : "y <[ x"
  shows "[^ x, y ^] = x"
proof-
  have 0 : "is_sup {x, y} x" using H
    by(auto simp add: has_sup_def is_sup_def is_least_def is_ub_def leq_refl)

  have 1: "is_bsup x y [^ x, y ^]" using bsup_spec by auto

  have 2 : "is_sup {x, y} [^ x, y ^]" using bsup_sup[OF 0 1] by auto

  show "[^ x, y ^] = x"
    using is_sup_unique[OF 0 2] by auto
qed


lemma bsup_base_eq :
  "[^ x, [^ x, y ^]^] = [^ x, y ^]"
proof-
  have 0: "x <[ [^ x, y ^]"
    using is_bsupD1[OF bsup_spec[of x y]] by auto

  show "[^ x, [^ x, y ^]^] = [^ x, y ^]"
    using bsup_base_leq[OF 0] by auto
qed

lemma bsup_arg_eq :
  "[^ [^ x, y ^], y ^] = [^ x, y ^]"
proof-
  have Eq1 : "[^ x, y ^] <[ [^ [^ x, y ^], y ^]"
    using is_bsupD1[OF bsup_spec] by auto

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

lemma ub_subset :
  assumes H : "is_ub S x"
  assumes H' : "S' \<subseteq> S"
  shows "is_ub S' x"
proof
  fix z
  assume Zin : "z \<in> S'"

  hence Zin' : "z \<in> S"
    using Zin H' by blast

  then show "z <[ x"
    using is_ubE[OF H Zin'] by simp
qed

lemma sup_subset_ub :
  assumes H : "is_sup S x"
  assumes H' : "S' \<subseteq> S"
  shows "is_ub S' x"
proof
  fix z
  assume Zin : "z \<in> S'"

  hence Zin' : "z \<in> S"
    using Zin H' by blast

  then show "z <[ x"
    using is_supD1[OF H Zin'] by simp
qed

lemma sup_ub :
  assumes H : "is_sup S x"
  shows "is_ub S x"
  using sup_subset_ub[OF H, of S]
  by auto

lemma is_sup_pair :
  assumes "a <[ b"
  shows "is_sup {a, b} b" using assms
  by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)


lemma sup_finite_all :
  assumes X_fin : "finite (X :: ('a :: Pordc_all) set)"
  assumes X_nemp : "x \<in> X"
  shows "has_sup X"
proof-
  obtain l where L: "set l = X"
    using finite_list[OF X_fin]
    by auto

  then show "has_sup X"
    using X_fin X_nemp
  proof(induction l arbitrary: X x)
    case Nil
    then show ?case by auto
  next
    case (Cons lh lt)
    then show ?case
    proof(cases lt)
      case Nil' : Nil

      have "is_sup X lh"
        using Cons.prems Nil' sup_singleton[of "lh"]
        by(auto)

      then show ?thesis 
        by(auto simp add: has_sup_def)
    next
      case Cons' : (Cons lh' lt')

      have Sub1 : "set lt' \<subseteq> insert lh' (set lt')"
        by auto

      have Sub2 : "insert lh' (set lt') \<subseteq> insert lh (insert lh' (set lt'))"
        by auto

      have Sub3 : "set lt' \<subseteq> insert lh (insert lh' (set lt'))"
        using Sub1 Sub2 by auto

      obtain slt where Slt: "is_sup (set lt) slt"
        using Cons.IH[OF refl _, of lh'] Cons'
        by(auto simp add: has_sup_def)

      obtain sl where Sl_alt : "is_sup {lh, slt} sl"
        using sup2_all[of lh slt]
        by(auto simp add: has_sup_def)

      have Lh_sup : "is_sup {lh} lh"
        using sup_singleton by auto
  
      have Conc' : "is_sup ({lh} \<union> (set lt)) sl"
        using sup_union1[OF Lh_sup Slt Sl_alt]
        by simp

      then have Conc'' : "is_sup (set (lh#lt)) sl"
        by auto

      then have Conc' : "is_sup X sl"
        using Cons.prems(1) Cons'
        by auto

      then show ?thesis
        by(auto simp add: has_sup_def)
    qed
  qed
qed


(* make sure we really need this before spending any more time trying to prove it *)

lemma sup_finite_pairwise :
  assumes X_fin : "finite (X :: ('a :: Pordpsc) set)"
  assumes X_nemp : "x \<in> X"
  assumes Nwise : "\<And> a b . a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> has_sup {a, b}"
  shows "has_sup X"
proof-

  obtain c where C: "c = card X"
    by auto

  show "has_sup X"
    using C X_fin X_nemp Nwise
  proof(induction c  arbitrary: X x rule: full_nat_induct)
    case (1 c)

    have IH :
      "\<And> m (x :: 'a set) xa. Suc m \<le> c \<Longrightarrow>
        m = card x \<Longrightarrow>
        finite x \<Longrightarrow>
        xa \<in> x \<Longrightarrow>
        (\<And> xa. xa \<in> x \<Longrightarrow>  (\<And> xb. xb \<in> x \<Longrightarrow> has_sup {xa, xb})) \<Longrightarrow>
                   has_sup x"
    proof-
      fix m :: nat
      fix x :: "'a set"
      fix xa :: 'a

      assume H1 :"Suc m \<le> c"
      assume H2 :"m = card (x :: 'a set)"
      assume H3 :"finite x"
      assume H4: "xa \<in> x"
      assume H5: "(\<And>xa. xa \<in> x \<Longrightarrow> (\<And>xb. xb \<in> x \<Longrightarrow> has_sup {xa, xb}))"
      show "has_sup x"
        using mp[OF spec[OF mp[OF mp[OF spec[OF mp[OF spec[OF 1(1), of m] H1]] H2] H3]] H4] H5
        by auto
    qed

    show ?case
    proof(cases c)
      case 0
  
      then have False using 1
        by auto
  
      then show ?thesis by auto
    next
      case (Suc c1)
      show ?thesis
      proof(cases c1)
        case Z1 : 0
  
        then have "card X = Suc 0"
          using 1 Suc
          by auto
  
        then obtain x1 where "X = {x1}"
          unfolding card_1_singleton_iff
          by(auto)
  
        then have "X = {x}"
          using 1
          by auto
  
        then have "is_sup X x"
          using sup_singleton[of x]
          by auto
  
        then show ?thesis
          by(auto simp add: has_sup_def)
      next
        case Suc1 : (Suc c2)
  
        then have Card_suc1 : "card X = Suc (Suc c2)"
          using 1 Suc
          by auto
  
        have Card_rest0 : "c1 = card (X - {x})"
          using card_Diff_singleton[OF 1(3) 1(4)]
            1 Suc Suc1
          by auto
  
        then have "0 < card (X - {x})"
          using Suc1 by auto
  
        then have "\<exists> x' . x' \<in> (X - {x})"
          unfolding card_gt_0_iff
          by(auto)
  
        then obtain x1 where X1 : "x1 \<in> (X)" "x1 \<noteq> x" "x1 \<in> (X - {x})"
          by(auto)
  
        have X_in_x1 : "x \<in> (X - {x1})"
          using 1(4) X1(2)
          by auto
  
        have Card_rest1 : "c1 = card (X - {x1})"
          using card_Diff_singleton[OF 1(3) X1(1)] Suc Suc1
            1
          by auto
  
        have Nwise0 : 
          "(\<And>a b. a \<in> (X - {x})\<Longrightarrow>
            b \<in> (X - {x}) \<Longrightarrow>
            has_sup {a, b})"
          using 1(5)
          by auto
  
        have Nwise1 :
          "(\<And>a b. a \<in> (X - {x1})\<Longrightarrow>
            b \<in> (X - {x1}) \<Longrightarrow>
            has_sup {a, b})"
          using 1(5)
          by auto

        show ?thesis
        proof(cases c2)
          case Z2 : 0

          then have "card X = 2"
            using 1(2) Suc Suc1
            by auto

          then obtain w1 w2 where W: "X = {w1, w2}" "w1 \<noteq> w2"
            unfolding card_2_iff
            by auto

          then show ?thesis
            using 1(5)[of w1 w2]
            by(auto)
        next
          case Suc2 : (Suc c3)

          then have Card_suc2 : "card X = Suc (Suc (Suc c3))"
            using 1 Suc Suc1
            by auto
    
          have Card_rest01 : "c2 = card ((X - {x}) - {x1})"
            using card_Diff_singleton[OF _ X1(3)]
              1 Suc Suc1 Suc2
            by auto
    
          then have "0 < card ((X - {x}) - {x1})"
            using Suc1 Suc2 by auto
    
          then have "\<exists> x' . x' \<in> ((X - {x}) - {x1})"
            unfolding card_gt_0_iff
            by(auto)
    
          then obtain x2 where X2 : "x2 \<in> (X)" "x2 \<noteq> x1" "x2 \<in> ((X - {x}) - {x1})"
            by(auto)

          have X2_x0 : "x2 \<noteq> x"
            using X2(3)
            by auto

          have Nwise2 :
            "(\<And>a b. a \<in> ((X - {x}) - {x1})\<Longrightarrow>
              b \<in> ((X - {x}) - {x1}) \<Longrightarrow>
              has_sup {a, b})"
            using 1(5)
            by auto

          have Nwise2' :
            "(\<And>a b. a \<in> (X - {x2})\<Longrightarrow>
              b \<in> (X - {x2}) \<Longrightarrow>
              has_sup {a, b})"
            using 1(5)
            by auto

          have "has_sup (X - {x})"
            using IH[OF _ Card_rest0 _ X1(3) Nwise0]
              Suc Suc1 1(3)
            by(auto)

          then obtain sup0 where Sup0 : "is_sup (X - {x}) sup0"
            by(auto simp add: has_sup_def)

          then obtain sup01 where Sup01: "is_sup ((X - {x}) - {x1}) sup01"
            using has_sup_subset[OF _ Sup0 _ X2(3)]
              1(3)
            by(auto simp add: has_sup_def)

          have X2_in_x1 : "x2 \<in> X - {x1}"
            using X2 X1 X2_x0
            by auto

          have "has_sup (X - {x1})"
            using IH[OF _ Card_rest1 _ X2_in_x1 Nwise1] 1(3)
              Suc Suc1 Suc2
            by auto

          then obtain sup1 where Sup1 : "is_sup (X - {x1}) sup1"
            by(auto simp add: has_sup_def)

          have X_in_x12 : "x \<in> X - {x1} - {x2}"
            using X2 X1 X2_x0 1(4)
            by auto

          then obtain sup12 where Sup12 : "is_sup ((X - {x1}) - {x2}) sup12"
            using has_sup_subset[OF _ Sup1 _ X_in_x12] 1(3)
            by(auto simp add: has_sup_def)

          have Card_rest2 : "c1 = card (X - {x2})"
            using card_Diff_singleton[OF 1(3) X2(1)] Suc Suc1
              1
            by auto

          have X1_x2 : "x1 \<in> X - {x2}"
            using X2 X1
            by auto

          have X1_in_x20 : "x1 \<in> X - {x2} - {x}"
            using X2 X1 X2_x0 1(4)
            by auto

          have "has_sup (X - {x2})"
            using IH[OF _ Card_rest2 _ X1_x2 Nwise2']
              Suc Suc1 Suc2 1(3)
            by(auto)

          then obtain sup2 where Sup2 : "is_sup (X - {x2}) sup2"
            by(auto simp add: has_sup_def)

          then obtain sup20 where Sup20: "is_sup ((X - {x2}) - {x}) sup20"
            using has_sup_subset[OF _ Sup2 _ X1_in_x20] 1(3)
            by(auto simp add: has_sup_def)

          have Unfold1 : "(X - {x} - {x1} \<union> (X - {x1} - {x2})) = (X - {x1})"
            using X2(2) X2_x0 X1(2)
            by(auto)

          have Sup0112 : "is_sup {sup01, sup12} sup1"
            using sup_union2[OF Sup01 Sup12, unfolded Unfold1, OF Sup1]
            by auto

          hence Hsup0112 : "has_sup {sup01, sup12}"
            by(auto simp add: has_sup_def)

          have Unfold2 : "(X - {x1} - {x2} \<union> (X - {x2} - {x})) = (X - {x2})"
            using X2(2) X2_x0 X1(2)
            by(auto)
 
          have Sup1220 : "is_sup {sup12, sup20} sup2"
            using sup_union2[OF Sup12 Sup20, unfolded Unfold2, OF Sup2]
            by auto

          hence Hsup1220 : "has_sup {sup12, sup20}"
            by(auto simp add: has_sup_def)

          have Unfold0 : "(X - {x} - {x1} \<union> (X - {x2} - {x})) = X - {x}"
            using X2(2) X2_x0 X1(2)
            by(auto)

          have Sup0120 : "is_sup {sup01, sup20} sup0"
            using sup_union2[OF Sup01 Sup20, unfolded Unfold0, OF Sup0]
            by auto

          hence Hsup0120 : "has_sup {sup01, sup20}"
            by(auto simp add: has_sup_def)

          obtain sup_final where Final :
            "is_sup {sup01, sup12, sup20} sup_final"
            using pairwise_sup[OF Hsup0112 Hsup1220 Hsup0120]
            by(auto simp add: has_sup_def)

          have Unfold_final0 : "({sup12, sup20} \<union> {sup01}) = {sup01, sup12, sup20}"
            by auto

          have Unfold_final :
            "(X - {x2} \<union> (X - {x} - {x1})) = X" 
            using X2(2) X2_x0 X1(2)
            by(auto)

          have Combine: "is_sup {sup2, sup01} sup_final"
            using sup_union2[OF Sup1220 sup_singleton[of sup01], unfolded Unfold_final0, OF Final] 
            by auto

          have "is_sup X sup_final"
            using sup_union1[OF Sup2 Sup01 Combine]
            unfolding Unfold_final
            by auto

          then show ?thesis
            by(auto simp add: has_sup_def)
        qed
      qed
    qed
  qed
qed
end