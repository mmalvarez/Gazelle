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


end