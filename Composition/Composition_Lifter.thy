theory Composition_Lifter
imports Composition "../Lifter/Lifter" "../Lifter/Lifter_Instances"

begin

(* This file contains lemmas for helping us prove sups_pres on
 * concrete examples of lifted functions.
 * The convenient thing is that we don't actually have to reason about the functions
 * themselves: just the lifting(s) being applied to them.
 *)


lemma l_ortho_sups_pres :
  fixes l1 :: "('x, 'a, 'b :: {Mergeable, Okay}, 'f1) lifting"
  fixes l2 :: "('x, 'a2, 'b, 'f2) lifting"
  assumes H : "l_ortho_pres l1 S1 l2 S2"
  assumes H1 : "lifting_valid_weak_pres l1 S1"
  assumes H2 : "lifting_valid_weak_pres l2 S2"
  shows "sups_pres {lift_map_s id l1 f1, lift_map_s id l2 f2} (\<lambda> x . S1 x \<inter> S2 x)"

proof
  fix el :: "'b"
  fix sup1 :: "'b"
  fix syn 
  fix Xs :: "'b set"
  fix Fs' :: "('x \<Rightarrow> 'b \<Rightarrow> 'b) set"
  fix f

  assume Hnemp_Xs : "el \<in> Xs"
  assume Subs : "Xs \<subseteq> S1 syn \<inter> S2 syn"
  assume Hfin_Xs : "finite Xs"
  assume H' : "is_sup Xs sup1"
  assume H'' : "sup1 \<in> S1 syn \<inter> S2 syn"
  assume Fs' : "Fs' \<subseteq> {lift_map_s id l1 f1, lift_map_s id l2 f2}"
  assume Hnemp_Fs' : "f \<in> Fs'"

  have In1 : "sup1 \<in> S1 syn" and In2 : "sup1 \<in> S2 syn"
    using H'' by auto

  have Sub1 : "Xs \<subseteq> S1 syn" and Sub2 : "Xs \<subseteq> S2 syn"
    using Subs by auto

  interpret LV1: lifting_valid_weak_pres l1 S1
    using H1 .

  interpret LV2: lifting_valid_weak_pres l2 S2
    using H2 .

  interpret Ortho: l_ortho_pres l1 S1 l2 S2
    using H .
  

  consider (Emp) "Fs' = {}" |
           (L1) "Fs' = {lift_map_s id l1 f1}" |
           (L2) "Fs' = {lift_map_s id l2 f2}" |
           (L1_2) "Fs' = {lift_map_s id l1 f1, lift_map_s id l2 f2}"
    using Fs' by blast
  then show
    "\<exists>sup'.
          is_sup ((\<lambda>f. f syn sup1) ` Fs') sup' \<and>
          is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) sup' \<and> sup' \<in> S1 syn \<inter> S2 syn"
  proof cases
  case Emp
    then show ?thesis using Hnemp_Fs' by auto
  next
    case L1

    have Conc1 : "is_sup ((\<lambda>f. f syn sup1) ` Fs') (lift_map_s id l1 f1 syn sup1)"
      using L1 sup_singleton
      by auto

    have L1' : "(scross ((\<lambda>f. f syn) ` Fs') Xs) = lift_map_s id l1 f1 syn ` Xs"
      unfolding L1 
      by(auto simp add: scross_def scross_singleton1)

(* TODO: syn version of l_ortho *)
    have Conc2 : "is_sup (lift_map_s id l1 f1 syn ` Xs) (lift_map_s id l1 f1 syn sup1)"
    proof(rule is_supI)
      fix y
      assume "y \<in> lift_map_s id l1 f1 syn ` Xs"

      then obtain x where Xin : "x \<in> Xs" and Xy : "lift_map_s id l1 f1 syn x = y"
        by blast

      have Xin' : "x \<in> S1 syn" using Subs Xin by auto

      have Sin' : "sup1 \<in> S1 syn" using H'' by auto

      have Leq1 : "x <[ sup1" using is_supD1[OF H' Xin] by simp

      have Pres : "is_sup (LMap l1 f1 syn ` Xs) (LMap l1 f1 syn sup1)"
        using LV1.pres[OF Xin _ H', of syn f1] H'' Subs
        by auto
 
      show "y <[ lift_map_s id l1 f1 syn sup1"
        unfolding sym[OF Xy]
        using is_supD1[OF Pres, of "lift_map_s id l1 f1 syn x"] Xin
        by(auto simp add: lift_map_s_def)
    next
      fix x'
      assume Ub : "is_ub (lift_map_s id l1 f1 syn ` Xs) x'"

      have Ub' : "is_ub ((\<lambda>f. f syn sup1) ` Fs') x'"
      proof(rule is_ubI)
        fix z
        assume Z : "z \<in> (\<lambda>f. f syn sup1) ` Fs'"

        then have Z' : "z = lift_map_s id l1 f1 syn sup1"
          using L1
          by auto

        have Pres : "is_sup (LMap l1 f1 syn ` Xs) (LMap l1 f1 syn sup1)"
          using  LV1.pres[OF Hnemp_Xs _ H', of syn f1] H'' Subs 
          by auto
 
        show "z <[ x'" using is_supD2[of _ z x', OF _ Ub] Pres unfolding lift_map_s_def Z'
          by auto
      qed

      show "lift_map_s id l1 f1 syn sup1 <[ x'"
        using is_supD2[OF Conc1, of x'] Ub'
        by(auto simp add: lift_map_s_def)
    qed

    have Result_S1 : "(lift_map_s id l1 f1 syn sup1) \<in> S1 syn"
      unfolding lift_map_s_def LMap_def
      apply(auto) (* NB: editing here *)
      using LV1.put_S by auto

    have Result_S2 : "(lift_map_s id l1 f1 syn sup1) \<in> S2 syn"
      unfolding lift_map_s_def LMap_def
      using Ortho.put1_S2[OF In2]
      by(auto)

    show ?thesis using Conc1 Conc2 Result_S1 Result_S2 unfolding L1 scross_singleton1 lift_map_s_def LMap_def
      using H''
      by(auto simp add:scross_singleton1)
  next

    case L2

    have Conc1 : "is_sup ((\<lambda>f. f syn sup1) ` Fs') (lift_map_s id l2 f2 syn sup1)"
      using L2 sup_singleton
      by auto

    have L2' : "(scross ((\<lambda>f. f syn) ` Fs') Xs) = lift_map_s id l2 f2 syn ` Xs"
      unfolding L2
      by(auto simp add: scross_def scross_singleton1)

(* TODO: syn version of l_ortho *)
    have Conc2 : "is_sup (lift_map_s id l2 f2 syn ` Xs) (lift_map_s id l2 f2 syn sup1)"
    proof(rule is_supI)
      fix y
      assume "y \<in> lift_map_s id l2 f2 syn ` Xs"

      then obtain x where Xin : "x \<in> Xs" and Xy : "lift_map_s id l2 f2 syn x = y"
        by blast

      have Xin' : "x \<in> S2 syn" using Subs Xin by auto

      have Sin' : "sup1 \<in> S2 syn" using H'' by auto

      have Leq1 : "x <[ sup1" using is_supD1[OF H' Xin] by simp

      have Pres : "is_sup (LMap l2 f2 syn ` Xs) (LMap l2 f2 syn sup1)"
        using LV2.pres[OF Xin _ H', of syn f2] H'' Subs
        by auto
 
      show "y <[ lift_map_s id l2 f2 syn sup1"
        unfolding sym[OF Xy]
        using is_supD1[OF Pres, of "lift_map_s id l2 f2 syn x"] Xin
        by(auto simp add: lift_map_s_def)
    next
      fix x'
      assume Ub : "is_ub (lift_map_s id l2 f2 syn ` Xs) x'"

      have Ub' : "is_ub ((\<lambda>f. f syn sup1) ` Fs') x'"
      proof(rule is_ubI)
        fix z
        assume Z : "z \<in> (\<lambda>f. f syn sup1) ` Fs'"

        then have Z' : "z = lift_map_s id l2 f2 syn sup1"
          using L2
          by auto

        have Pres : "is_sup (LMap l2 f2 syn ` Xs) (LMap l2 f2 syn sup1)"
          using  LV2.pres[OF Hnemp_Xs _ H', of syn f2] H'' Subs 
          by auto
 
        show "z <[ x'" using is_supD2[of _ z x', OF _ Ub] Pres unfolding lift_map_s_def Z'
          by auto
      qed

      show "lift_map_s id l2 f2 syn sup1 <[ x'"
        using is_supD2[OF Conc1, of x'] Ub'
        by(auto simp add: lift_map_s_def)
    qed

    have Result_S1 : "(lift_map_s id l2 f2 syn sup1) \<in> S2 syn"
      unfolding lift_map_s_def LMap_def
      using LV2.put_S by auto

    have Result_S2 : "(lift_map_s id l2 f2 syn sup1) \<in> S1 syn"
      unfolding lift_map_s_def LMap_def
      using Ortho.put2_S1[OF In1]
      by(auto)

    show ?thesis using Conc1 Conc2 Result_S1 Result_S2 unfolding L2 scross_singleton1 lift_map_s_def LMap_def
      using H''
      by(auto simp add:scross_singleton1)
  next

    case L1_2
(* YOU ARE HERE 
looks like maybe we need some kind of idem thing... otherwise we aren't going to
be able to show set membership.*)

    have Res_sup :
      "is_sup {(lift_map_s id l1 f1 syn sup1), (lift_map_s id l2 f2 syn sup1)} (LMap l1 f1 syn (LMap l2 f2 syn sup1))"
      using Ortho.compat_pres_sup unfolding lift_map_s_def LMap_def has_sup_def
      by(auto simp add: Ortho.put2_get1)

    hence Conc1 : "is_sup {(lift_map_s id l1 f1 syn sup1), (lift_map_s id l2 f2 syn sup1)}
      [^ (lift_map_s id l1 f1 syn sup1), (lift_map_s id l2 f2 syn sup1)^]"
      using bsup_sup[OF Res_sup bsup_spec] by auto

    have Conc2 : "is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs)
        [^ (lift_map_s id l1 f1 syn sup1), (lift_map_s id l2 f2 syn sup1)^]"
    proof(rule is_supI)

      fix x

      assume "x \<in> scross ((\<lambda>f. f syn) ` Fs') Xs"

      then have "x \<in> ((lift_map_s id l1 f1 syn) ` Xs) \<union> ((lift_map_s id l2 f2 syn) ` Xs)"
        unfolding L1_2 scross_def
        by(auto)

      then consider (Xin_1) xo where "xo \<in> Xs" "x = lift_map_s id l1 f1 syn xo" |
                    (Xin_2) xo where "xo \<in> Xs" "x = lift_map_s id l2 f2 syn xo"
        by blast

      then show "x <[ [^ lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1 ^]"
      proof cases

        case Xin_1

        have Map_sup : "is_sup (LMap l1 f1 syn ` Xs) (LMap l1 f1 syn sup1)"
          using LV1.pres[OF Hnemp_Xs Sub1 H' In1] by auto

        have Leq1 : "x <[ lift_map_s id l1 f1 syn sup1"
          using is_supD1[OF Map_sup, of x] Xin_1
          unfolding lift_map_s_def
          by(auto)

        have Leq2 : "lift_map_s id l1 f1 syn sup1 <[ [^ lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1 ^]"
          using is_supD1[OF Conc1, of "lift_map_s id l1 f1 syn sup1"] 
          by auto

        show ?thesis
          using leq_trans[OF Leq1 Leq2]
          by auto
      next
        case Xin_2

        have Map_sup : "is_sup (LMap l2 f2 syn ` Xs) (LMap l2 f2 syn sup1)"
          using LV2.pres[OF Hnemp_Xs Sub2 H' In2] by auto

        have Leq1 : "x <[ lift_map_s id l2 f2 syn sup1"
          using is_supD1[OF Map_sup, of x] Xin_2
          unfolding lift_map_s_def
          by(auto)

        have Leq2 : "lift_map_s id l2 f2 syn sup1 <[ [^ lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1 ^]"
          using is_supD1[OF Conc1, of "lift_map_s id l2 f2 syn sup1"] 
          by auto

        show ?thesis
          using leq_trans[OF Leq1 Leq2]
          by auto
      qed
    next

      fix x'

      assume Ub: "is_ub (scross ((\<lambda>f. f syn) ` Fs') Xs) x'"

      
      have Ub': "is_ub {(lift_map_s id l1 f1 syn sup1), (lift_map_s id l2 f2 syn sup1)} x'"
      proof(rule is_ubI)

        fix w

        assume W: "w \<in> {lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1}"

        then consider (W1) "w = lift_map_s id l1 f1 syn sup1" |
                      (W2) "w = lift_map_s id l2 f2 syn sup1" by auto

        then show "w <[ x'"
        proof cases

          case W1

          have Pres : "is_sup (LMap l1 f1 syn ` Xs) (LMap l1 f1 syn sup1)"
            using LV1.pres[OF Hnemp_Xs _ H', of syn f1] H'' Subs
            by auto

          have Sub : "(LMap l1 f1 syn ` Xs) \<subseteq> (scross ((\<lambda>f. f syn) ` Fs') Xs)"
            unfolding scross_def L1_2 lift_map_s_def
            by(fastforce)

          have Ub_W1 : "is_ub (LMap l1 f1 syn ` Xs) x'"
            using ub_subset[OF Ub Sub] by simp

          show ?thesis
            using is_supD2[OF Pres Ub_W1] W1
            unfolding lift_map_s_def
            by auto
        next
          case W2

          have Pres : "is_sup (LMap l2 f2 syn ` Xs) (LMap l2 f2 syn sup1)"
            using LV2.pres[OF Hnemp_Xs _ H', of syn f2] H'' Subs
            by auto

          have Sub : "(LMap l2 f2 syn ` Xs) \<subseteq> (scross ((\<lambda>f. f syn) ` Fs') Xs)"
            unfolding scross_def L1_2 lift_map_s_def
            by(fastforce)

          have Ub_W2 : "is_ub (LMap l2 f2 syn ` Xs) x'"
            using ub_subset[OF Ub Sub] by simp

          show ?thesis
            using is_supD2[OF Pres Ub_W2] W2
            unfolding lift_map_s_def
            by auto
        qed
      qed

      show "[^ lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1 ^] <[ x'"
        using is_supD2[OF Conc1 Ub'] by auto
    qed

    have Sups_eq : "[^ lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1 ^] = LMap l1 f1 syn (LMap l2 f2 syn sup1)"
      using is_sup_unique[OF Res_sup Conc1]
      by auto

    have Sup1_in1_2 :
      "sup1 \<in> S1 syn" "sup1 \<in> S2 syn"
      using H'' by auto

    have Sup1_in1_alt : "LMap l1 f1 syn (LMap l2 f2 syn sup1) \<in> S1 syn"
      using LV1.put_S Ortho.put2_S1[OF Sup1_in1_2(1)]
      by(auto)

    have Sup1_in2_alt : "LMap l1 f1 syn (LMap l2 f2 syn sup1) \<in> S2 syn"
      using Ortho.put1_S2[OF LV2.put_S]
      by auto

    have Sup1_in_alt : "LMap l1 f1 syn (LMap l2 f2 syn sup1) \<in> S1 syn \<inter> S2 syn"
      using Sup1_in1_alt Sup1_in2_alt
      by auto

    have Result_In :
      "[^ lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1 ^] \<in> S1 syn \<inter> S2 syn"
      unfolding Sups_eq using Sup1_in_alt
      by(auto)

    show ?thesis using Conc1 Conc2 Result_In unfolding L1_2 lift_map_s_def LMap_def
      using H''
      by(auto simp add:scross_def)
  qed
qed

lemma merge_lift_pcomps : 
  fixes l1 l2 f1 f2 s x S
  assumes H : "l_ortho_pres l1 S1 l2 S2"
  shows "LMap (merge_l l1 l2) (f1, f2) s x = pcomps [LMap l1 f1, LMap l2 f2] s x"
proof-
  interpret Ortho: l_ortho_pres l1 S1 l2 S2
    using H .

  have Sup : "is_sup {LMap l1 f1 s x, LMap l2 f2 s x} (LMap (merge_l l1 l2) (f1, f2) s x)"
    using Ortho.compat_pres_sup
    by(auto simp add: merge_l_def)

  have Sup' : "is_sup {LMap l1 f1 s x, LMap l2 f2 s x} [^LMap l1 f1 s x, LMap l2 f2 s x^]"
    using bsup_sup[OF Sup bsup_spec]
    by auto

  have Eq : "(LMap (merge_l l1 l2) (f1, f2) s x) = [^LMap l1 f1 s x, LMap l2 f2 s x^]"
    using is_sup_unique[OF Sup Sup']
    by auto

  then show
    "LMap (merge_l l1 l2) (f1, f2) s x = pcomps [LMap l1 f1, LMap l2 f2] s x"
    by auto
qed

(* ok, we further need to know that f is sups_pres on its own. how can we prove that
 * for our lifted functions?
 *)
lemma lifting_pres :
  assumes H : "lifting_valid_weak_pres l S"
  shows "sups_pres {LMap l f} S"
proof(rule sups_presI)
  fix x supr :: 'c
  fix Xs :: "'c set"
  fix Fs'
  fix syn
  fix g

  assume Xin : "x \<in> Xs"
  assume Xsub : "Xs \<subseteq> S syn"
  assume Fin_Xs : "finite Xs"
  assume Supr : "is_sup Xs supr"
  assume Supr_in : "supr \<in> S syn"
  assume Fs'_sub : "Fs' \<subseteq> {LMap l f}"
  assume G: "g \<in> Fs'"

  interpret LV : lifting_valid_weak_pres l S
    using H.

  have Fs' : "Fs' = {LMap l f}"
    using Fs'_sub G
    by auto

  have Suprf : "is_sup (LMap l f syn ` Xs) (LMap l f syn supr)"
    using LV.pres[OF Xin Xsub Supr Supr_in]
    by auto

  have Conc1 : "is_sup ((\<lambda>f. f syn supr) ` Fs') (LMap l f syn supr)"
    unfolding Fs'
    using sup_singleton[of "(LMap l f syn supr)"]
    by auto

  have Cross : "(scross ((\<lambda>f. f syn) ` Fs') Xs) = LMap l f syn ` Xs"
    unfolding Fs'
    by(auto simp add: scross_def)

  have Conc2 : "is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) (LMap l f syn supr)"
    unfolding Cross 
    using Suprf
    by auto

  have Conc3 : "LMap l f syn supr \<in> S syn"
    using LV.put_S
    by auto

  show "\<exists>sup'.
          is_sup ((\<lambda>f. f syn supr) ` Fs') sup' \<and>
          is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) sup' \<and> sup' \<in> S syn"
    using Conc1 Conc2 Conc3
    by auto
qed

lemma nwise_sup :
  fixes x :: "'a :: Pordpsc"
  assumes Fin : "finite Xs"
  assumes Sup_Xs : "is_sup Xs y"
  assumes Nwise : "\<And> z . z \<in> Xs \<Longrightarrow> has_sup {x, z}"
  shows "has_sup (Xs \<union> {x})"
proof-
  obtain l where L: "set l = Xs"
    using finite_list[OF Fin]
    by(auto)

  then have Sup_Xs' : "is_sup (set l) y"
    using Sup_Xs by auto

  have Nwise' : "\<And> z . z \<in> set l \<Longrightarrow> has_sup {x, z}"
    using L Nwise
    by auto

  have Conc' : "has_sup (set(x#l))"
    using Sup_Xs' Nwise' 
  proof(induction l arbitrary: x y)
    case Nil
    then show ?case 
      using sup_singleton[of x]
      by(auto simp add: has_sup_def)
  next
    case (Cons w l')

    show ?case
    proof(cases l')
      case Nil' : Nil
      then show ?thesis using Cons.prems(2)[of w]
        by auto
    next
      case Cons' : (Cons w' l'')

      have Sub1 :  "(set l'' \<subseteq> (insert w' (set l'')))"
        using subset_insertI by auto

      have Sub2 : "(insert w' (set l'')) \<subseteq> insert w (insert w' (set l''))"
        using subset_insertI by auto

      have Sub3 : "set l'' \<subseteq> insert w (insert w' (set l''))"
        using Sub1 Sub2
        by auto

      obtain sl' where Sup_l' : "is_sup (set l') sl'"
        using has_sup_subset[OF _ Cons.prems(1), of "set l'" w'] Cons' Sub3
        by(auto simp add: has_sup_def)

      have Nwise'' : "(\<And>z. z \<in> set l' \<Longrightarrow> has_sup {x, z})"
        using Cons.prems(2)
        by auto

      have Sup_x : "is_sup {x} x"
        using sup_singleton by auto

      have Sup_w : "is_sup {w} w"
        using sup_singleton by auto

      obtain sxl' where Sup_x_l' : "is_sup (set (x # l')) sxl'"
        using Cons.IH[OF Sup_l' Nwise'']
        by( auto simp add: has_sup_def)

      then have Sup_x_l'_alt : "is_sup ( {x} \<union> set l') sxl'"
        by auto

      obtain swl' where Sup_w_l' : "is_sup (set (w#l')) swl'"
        using Cons.prems by auto

      then have Sup_w_l'_alt : "is_sup ( {w} \<union> set l') swl'"
        by auto

      obtain sxw where Sup_x_w : "is_sup {x, w} sxw"
        using Cons.prems(2)[of w]
        by(auto simp add: has_sup_def)
      hence Hsup_x_w : "has_sup {x, w}"
        using has_sup_def by auto

      have Sup_x_sup_l' : "is_sup {x, sl'} sxl'"
        using sup_union2[OF Sup_x Sup_l' Sup_x_l'_alt] by auto
      hence Hsup_x_sup_l' : "has_sup {x, sl'}"
        using has_sup_def by auto

      have Sup_w_sup_l' : "is_sup {w, sl'} swl'"
        using sup_union2[OF Sup_w Sup_l' Sup_w_l'_alt] by auto
      hence Hsup_w_sup_l' : "has_sup {w, sl'}"
        using has_sup_def by auto

      obtain sxwl' where Sup_all : "is_sup {x, w, sl'} sxwl'"
        using pairwise_sup[OF Hsup_x_w Hsup_w_sup_l' Hsup_x_sup_l']
        by(auto simp add: has_sup_def)

      have "{x, w} \<union> {sl'} = {x, w, sl'}"
        by auto

      then have Sup_all2 : "is_sup {sxw, sl'} sxwl'"
        using sup_union2[OF Sup_x_w sup_singleton, of sl' sxwl'] Sup_all
        by auto

      have "set (x # w # l') = ({x, w} \<union> set l')"
        by auto

      then show ?thesis
        using sup_union1[OF Sup_x_w Sup_l' Sup_all2]
        by(auto simp add: has_sup_def)
    qed
  qed

  then show "has_sup (Xs \<union> {x})" using L
    by(auto)
qed

lemma nwise_sups :
  fixes Xs1 Xs2 :: "('a :: Pordpsc) set"
  assumes Fin1 : "finite Xs1"
  assumes Fin2 : "finite Xs2"
  assumes Sup_Xs1 : "is_sup Xs1 y1"
  assumes Sup_Xs2 : "is_sup Xs2 y2"
  assumes Nwise : "\<And> z1 z2 . z1 \<in> Xs1 \<Longrightarrow> z2 \<in> Xs2 \<Longrightarrow> has_sup {z1, z2}"
  shows "has_sup (Xs1 \<union> Xs2)"
proof-

  obtain l2 where L2: "set l2 = Xs2"
    using finite_list[OF Fin2]
    by(auto)

  then have Sup_Xs2' : "is_sup (set l2) y2"
    using Sup_Xs2 by auto

  have Nwise' : "\<And> z1 z2 . z1 \<in> Xs1 \<Longrightarrow> z2 \<in> set l2 \<Longrightarrow> has_sup {z1, z2}"
    using L2 Nwise
    by auto

  have Conc' : "has_sup (Xs1 \<union> set l2)"
    using Sup_Xs1 Sup_Xs2' Nwise' 
  proof(induction l2 arbitrary: y1 y2)
    case Nil
    then show ?case 
      by(auto simp add: has_sup_def)
  next
    case (Cons w2 l2')

    show ?case
    proof(cases l2')
      case Nil' : Nil

      have Nwise : "(\<And>z. z \<in> Xs1 \<Longrightarrow> has_sup {w2, z})"
      proof-
        fix z
        assume Z : "z \<in> Xs1"

        have Comm : "{w2, z} = {z, w2}" by auto
        show "has_sup {w2, z}" using Cons.prems(3)[OF Z, of w2] unfolding Comm
          by auto
      qed

      have Conc' : "has_sup (Xs1 \<union> {w2})"
        using nwise_sup[OF Fin1 Cons.prems(1) Nwise] 
        by auto

      then show ?thesis using Nil'
        by auto
    next
      case Cons' : (Cons w2' l'')

      obtain sup2' where Sup2' : 
        "is_sup (set l2') sup2'" 
        using has_sup_subset[OF _ Cons.prems(2), of "set l2'" w2'] Cons'
        by (auto simp add: has_sup_def)

      have Nwise : "(\<And>z1 z2. z1 \<in> Xs1 \<Longrightarrow> z2 \<in> set l2' \<Longrightarrow> has_sup {z1, z2})"
      proof-
        fix z1 z2
        assume Z1 : "z1 \<in> Xs1"
        assume Z2 : "z2 \<in> set l2'"

        then have Z2' : "z2 \<in> set (w2#l2')"
          by auto

        show "has_sup {z1, z2}" using Cons.prems(3)[OF Z1 Z2']
          by auto
      qed

      obtain sup_Xs1_l2 where Sup_Xs1_l2 : "is_sup (Xs1 \<union> set l2') sup_Xs1_l2"
        using Cons.IH[OF Cons.prems(1) Sup2' Nwise]
        by(auto simp add: has_sup_def)

      have Fin_Xs1_l2 :
        "finite (Xs1 \<union> set l2')"
        using Fin1
        by(auto)

      have Nwise' : "(\<And>z. z \<in> Xs1 \<union> set l2' \<Longrightarrow> has_sup {w2, z})"
      proof-
        fix z
        assume Z: "z \<in> Xs1 \<union> set l2'"

        then consider (1) "z \<in> Xs1" | (2) "z \<in> set l2'"
          by auto
        then show "has_sup {w2, z}"
        proof cases
          case 1

          have Conc' : "has_sup {z, w2}"
            using Cons.prems(3)[OF 1, of w2]
            by auto

          have Comm : "{z, w2} = {w2, z}"
            by auto

          then show ?thesis
            using Conc' unfolding Comm
            by auto
        next
          case 2

          then show ?thesis
            using has_sup_subset[OF _ Cons.prems(2), of "{w2, z}" w2]
            by auto
        qed
      qed

      have Conc' : "has_sup ((Xs1 \<union> set l2') \<union> {w2})"
        using nwise_sup[OF Fin_Xs1_l2 Sup_Xs1_l2 Nwise']
        by auto

      have Comm : "((Xs1 \<union> set l2') \<union> {w2}) = (Xs1 \<union> set (w2 # l2'))"
        by auto

      show ?thesis using Conc' unfolding Comm
        by auto
    qed
  qed

  then show "has_sup (Xs1 \<union> Xs2)"
    unfolding L2
    by auto
qed

(* this is how we merge functions that don't obey the stricter criteria of
 * being l_ortho. (e.g. prio's that update the same field)
 *)
lemma sups_pres_insert :
  fixes Fs
  fixes f
  fixes S :: "'syn \<Rightarrow> ('x :: Mergeableps) set"
  assumes Hf : "sups_pres {f} S"
  assumes HFs : "sups_pres (set fs) S"
  assumes Pairwise : "\<And> g . g \<in> set fs \<Longrightarrow> sups_pres {g, f} S"
  shows "sups_pres (set (f#fs) ) S"
  using Hf HFs Pairwise
proof(induction fs arbitrary: f)
  case Nil
  then show ?case using Hf
    by auto
next
  case (Cons g fs')

  show ?case
  proof(cases fs')
    case Nil' : Nil

    have Comm : "{g, f} = {f, g}"
      by auto

    have "sups_pres {g, f} S"
      using Cons.prems(3)[of g]
      by auto

    then have "sups_pres {f, g} S"
      unfolding Comm
      by auto

    then show ?thesis using Nil'
      by(auto)
  next
    case Cons' : (Cons g' fs'')
    show ?thesis 
    proof(rule sups_presI)
      fix x supr :: 'x
      fix Xs :: "'x set"
      fix Fs'
      fix syn
      fix h
      assume "x \<in> Xs"
      assume Xin : "x \<in> Xs"
      assume Xsub : "Xs \<subseteq> S syn"
      assume Fin_Xs : "finite Xs"
      assume Supr : "is_sup Xs supr"
      assume Supr_in : "supr \<in> S syn"
      assume Fs'_sub : "Fs' \<subseteq> set (f # g # fs')"
      assume G: "h \<in> Fs'"
  
      have Pres_fs' : "sups_pres (set fs') S"
        using sups_pres_subset[OF Cons.prems(2), of "set fs'" g']
        using Cons'
        by auto

      obtain fs'_sup where Fs'_sup :
        "is_sup ((\<lambda>f. f syn supr) ` set (fs')) fs'_sup"
        "is_sup (scross ((\<lambda>f. f syn) ` set (fs')) Xs) fs'_sup"
        "fs'_sup \<in> S syn"
        using sups_presD[OF Pres_fs' Xin Xsub Fin_Xs Supr Supr_in _, of "set fs'" g'] Cons'
        by auto

      have Nwise : "(\<And>k. k \<in> set fs' \<Longrightarrow> sups_pres {k, f} S)"
      proof-
        fix k
        assume K: "k \<in> set fs'"

        then have K' : "k \<in> set (g # fs')"
          by auto

        show "sups_pres {k, f} S"
          using Cons.prems(3)[OF K']
          by auto
      qed

      have Pres_f_fs' : "sups_pres (set (f # fs')) S" using 
          Cons.IH[OF Cons.prems(1) Pres_fs' Nwise]
        by auto

      have Pres_g_fs' : "sups_pres (set (g # fs')) S"
        using Cons.prems by auto

      have F_fs_arg1 : "set (f # fs') \<subseteq> set (f # fs')"
        by auto

      have F_fs_arg2 : "f \<in> set (f# fs')"
        by auto

      obtain f_fs'_sup where F_fs'_sup:
        "is_sup ((\<lambda>f. f syn supr) ` set (f # fs')) f_fs'_sup"
        "is_sup (scross ((\<lambda>f. f syn) ` set (f # fs')) Xs) f_fs'_sup"
        "f_fs'_sup \<in> S syn"
        using sups_presD[OF Pres_f_fs' Xin Xsub Fin_Xs Supr Supr_in F_fs_arg1 F_fs_arg2]
        by auto

      have G_fs_arg1 : "set (g # fs') \<subseteq> set (g # fs')"
        by auto

      have G_fs_arg2 : "g \<in> set (g# fs')"
        by auto

      obtain g_fs'_sup where G_fs'_sup :
        "is_sup ((\<lambda> f . f syn supr) ` set (g#fs')) g_fs'_sup"
        "is_sup (scross ((\<lambda> f . f syn) ` set (g # fs')) Xs) g_fs'_sup"
        "g_fs'_sup \<in> S syn"
        using sups_presD[OF Pres_g_fs' Xin Xsub Fin_Xs Supr Supr_in G_fs_arg1 G_fs_arg2]
        by auto

      have Comm : "{g, f} = {f, g}"
        by auto

      have Pres_f_g : 
        "sups_pres {f, g} S"
        using Cons.prems(3)[of g]
        unfolding Comm
        by auto

      obtain f_g_sup where F_g_sup :
        "is_sup ((\<lambda> f . f syn supr) ` set ([f, g])) f_g_sup" 
        "is_sup (scross ((\<lambda> f . f syn) ` set ([f, g])) Xs) f_g_sup"
        "f_g_sup \<in> S syn"
        using sups_presD[OF Pres_f_g Xin Xsub Fin_Xs Supr Supr_in, of "{f, g}" f]
        by auto

      consider (No_f_no_g) "f \<notin> Fs'" "g \<notin> Fs'" |
               (F_no_g) "f \<in> Fs'" "g \<notin> Fs'" |
               (No_f_g) "f \<notin> Fs'" "g \<in> Fs'" |
               (F_g) "f \<in> Fs'" "g \<in> Fs'"
        by auto
      then show "\<exists>sup'.
            is_sup ((\<lambda>f. f syn supr) ` Fs') sup' \<and>
            is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) sup' \<and> sup' \<in> S syn"
      proof cases
        case No_f_no_g

        then have Fs'_sub' : "Fs' \<subseteq> set fs'"
          using Fs'_sub by auto

        then have Conc' : "sups_pres Fs' S"
          using sups_pres_subset[OF Pres_fs' _ Fs'_sub' G]
          by auto

        then show ?thesis
          using sups_presD[OF Conc' Xin Xsub Fin_Xs Supr Supr_in _ G]
          by auto
      next
        case F_no_g
        then have Fs'_sub' : "Fs' \<subseteq> set (f#fs')"
          using Fs'_sub by auto

        then show ?thesis
          using sups_presD[OF Pres_f_fs' Xin Xsub Fin_Xs Supr Supr_in _ G]
          by auto
      next
        case No_f_g
        then have Fs'_sub' : "Fs' \<subseteq> set (g#fs')"
          using Fs'_sub by auto

        then show ?thesis
          using sups_presD[OF Pres_g_fs' Xin Xsub Fin_Xs Supr Supr_in _ G]
          by auto
      next
        case F_g 
        show ?thesis
        proof(cases "f = g")
          case True

          then have Fs'_sub' : "Fs' \<subseteq> set (f # fs')"
            using Fs'_sub
            by auto

          obtain f_fs'_sup where F_fs'_sup:
            "is_sup ((\<lambda>f. f syn supr) ` Fs') f_fs'_sup"
            "is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) f_fs'_sup"
            "f_fs'_sup \<in> S syn"
            using sups_presD[OF Pres_f_fs' Xin Xsub Fin_Xs Supr Supr_in Fs'_sub' F_g(1)]
            by auto

          then show ?thesis
            by auto
        next
          case False

          have F_remain : "f \<in> Fs' - {g}"
            using F_g False by auto

          have G_remain : "g \<in> Fs' - {f}"
            using F_g False by auto

          have F_fs_arg1 : "Fs' - {g} \<subseteq> set (f # fs')"
            using Fs'_sub
            by auto

          have G_fs_arg1 : "Fs' - {f} \<subseteq> set (g # fs')"
            using Fs'_sub
            by auto

          obtain f_fs'_sup' where F_fs'_sup':
            "is_sup ((\<lambda>f. f syn supr) ` (Fs' - {g})) f_fs'_sup'"
            "is_sup (scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs) f_fs'_sup'"
            "f_fs'_sup' \<in> S syn"
            using sups_presD[OF Pres_f_fs' Xin Xsub Fin_Xs Supr Supr_in F_fs_arg1 F_remain]
            by auto

          obtain g_fs'_sup' where G_fs'_sup' :
            "is_sup ((\<lambda> f . f syn supr) ` (Fs' - {f})) g_fs'_sup'"
            "is_sup (scross ((\<lambda> f . f syn) ` (Fs' - {f})) Xs) g_fs'_sup'"
            "g_fs'_sup' \<in> S syn"
            using sups_presD[OF Pres_g_fs' Xin Xsub Fin_Xs Supr Supr_in G_fs_arg1 G_remain ]
            by auto

          have Fs'_fin : "finite Fs'"
            using finite_subset[OF Fs'_sub]
            by auto

          have Nwise1 : " (\<And>z1 z2.
            z1 \<in> (\<lambda>f. f syn supr) ` (Fs' - {g}) \<Longrightarrow>
            z2 \<in> (\<lambda>f. f syn supr) ` (Fs' - {f}) \<Longrightarrow>
            has_sup {z1, z2})"
          proof-
            fix z1 z2
            assume Z1 : "z1 \<in> (\<lambda>f. f syn supr) ` (Fs' - {g})"
            assume Z2 : "z2 \<in> (\<lambda> f . f syn supr) ` (Fs' - {f})"
  
            consider (Z1_f) "z1 = f syn supr" |
                     (Z1_fs) f'1 where "f'1 \<in> Fs'" "z1 = f'1 syn supr" "f'1 \<noteq> g" "f'1 \<noteq> f"
              using Z1 False
              by auto
  
            then show "has_sup {z1, z2}"
            proof cases
              case Z1_f
  
              consider (Z2_g) "z2 = g syn supr" | 
                       (Z2_fs) f'2 where "f'2 \<in> Fs'" "z2 = f'2 syn supr" "f'2 \<noteq> f" "f'2 \<noteq> g"
                using Z2 False
                by auto
  
              then show ?thesis
              proof cases
                case Z2_g
                then show ?thesis using Z1_f
                  using F_g_sup(1)
                  by(auto simp add: has_sup_def)
              next
                case Z2_fs
  
                have Sub : "{z1, z2} \<subseteq> ((\<lambda>f. f syn supr) ` (Fs' - {g}))"
                  using Z1_f Z2_fs F_g False
                  by auto
  
                then show ?thesis using has_sup_subset[OF _ F_fs'_sup'(1) Sub, of z1] Fs'_fin
                  by auto
              qed
  
            next
              case Z1_fs
              consider (Z2_g) "z2 = g syn supr" | 
                       (Z2_fs) f'2 where "f'2 \<in> Fs'" "z2 = f'2 syn supr" "f'2 \<noteq> g" "f'2 \<noteq> f"
                using Z2
                by auto
  
              then show ?thesis
              proof cases
                case Z2_g
  
                have Sub : "{z1, z2} \<subseteq> ((\<lambda>f. f syn supr) ` (Fs' - {f}))"
                  using Z1_fs Z2_g F_g False
                  by auto
  
                then show ?thesis using Z1_fs Z2_g
                  using has_sup_subset[OF _ G_fs'_sup'(1) Sub] Fs'_fin
                  by(auto simp add: has_sup_def)
              next
                case Z2_fs
  
                have Sub : "{z1, z2} \<subseteq> ((\<lambda>f. f syn supr) ` (Fs' - {g}))"
                  using Z1_fs Z2_fs
                  by auto
  
                then show ?thesis using has_sup_subset[OF _ F_fs'_sup'(1) Sub, of "z1"] Fs'_fin
                  by auto
              qed
            qed
          qed
  
          have Nwise2 : "(\<And>z1 z2.
                          z1 \<in> scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs \<Longrightarrow>
                          z2 \<in> scross ((\<lambda>f. f syn) ` (Fs' - {f})) Xs \<Longrightarrow>
                          has_sup {z1, z2})"
          proof-
            fix z1 z2
            assume Z1 : "z1 \<in> scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs"
            assume Z2 : "z2 \<in> scross ((\<lambda>f. f syn) ` (Fs' - {f})) Xs"

            consider (Z1_f) x1 where "x1 \<in> Xs" "z1 = f syn x1" |
                     (Z1_fs) x1 f'1 where "x1 \<in> Xs" "f'1 \<in> Fs'" "z1 = f'1 syn x1" "f'1 \<noteq> f" "f'1 \<noteq> g"
              using Z1 False
              by(auto simp add: scross_def)
  
            then show "has_sup {z1, z2}"
            proof cases
              case Z1_f
  
              consider (Z2_g) x2 where "x2 \<in> Xs" "z2 = g syn x2" | 
                       (Z2_fs) x2 f'2 where "x2 \<in> Xs" "f'2 \<in> Fs'" "z2 = f'2 syn x2" "f'2 \<noteq> f" "f'2 \<noteq> g"
                using Z2 False
              by(auto simp add: scross_def)
  
              then show ?thesis
              proof cases
                case Z2_g
  
  
                have Sub: "{z1, z2} \<subseteq> (scross ((\<lambda>f. f syn) ` set [f, g]) Xs)"
                  using Z1_f Z2_g
                  by(auto simp add: scross_def)
  
                have Fin: "finite (scross ((\<lambda>f. f syn) ` set [f, g]) Xs)"
                  using scross_finite[OF _ Fin_Xs, of "((\<lambda>f. f syn) ` set [f, g])"]
                  by auto
  
                show ?thesis using Z1_f Z2_g
                  using has_sup_subset[OF Fin F_g_sup(2) Sub, of z1]
                  by(auto)
              next
                case Z2_fs
  
                have Sub : "{z1, z2} \<subseteq> (scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs)"
                  using Z1_f Z2_fs F_g False
                  by(auto simp add: scross_def)
                  
                have Fin : "finite (scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs)"
                  using scross_finite[OF _ Fin_Xs, of "((\<lambda>f. f syn) ` (Fs' - {g}))"] Fs'_fin
                  by auto
  
                then show ?thesis using has_sup_subset[OF _ F_fs'_sup'(2) Sub]
                  by auto
              qed
            next
              case Z1_fs
              consider (Z2_g) x2 where "x2 \<in> Xs" "z2 = g syn x2" | 
                       (Z2_fs) x2 f'2 where "x2 \<in> Xs" "f'2 \<in> Fs'" "z2 = f'2 syn x2" "f'2 \<noteq> f" "f'2 \<noteq> g"
                using Z2 False
              by(auto simp add: scross_def)
  
              then show ?thesis
              proof cases
                case Z2_g
  
                have Sub : "{z1, z2} \<subseteq> (scross ((\<lambda>f. f syn) ` (Fs' - {f})) Xs)"
                  using Z1_fs Z2_g F_g False
                  by (auto simp add: scross_def)
  
                have Fin : "finite (scross ((\<lambda> f . f syn) ` (Fs' - {f})) Xs)"
                  using scross_finite[OF _ Fin_Xs, of "(\<lambda> f . f syn) ` (Fs' - {f})"] Fs'_fin
                  by auto
  
                then show ?thesis using has_sup_subset[OF _ G_fs'_sup'(2) Sub]
                  by(auto simp add: has_sup_def)
              next
                case Z2_fs
  
                have Sub : "{z1, z2} \<subseteq> (scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs)"
                  using Z1_fs Z2_fs F_g False
                  by (auto simp add: scross_def)
  
                have Fin : "finite (scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs)"
                  using scross_finite[OF _ Fin_Xs, of "(\<lambda>f. f syn) ` (Fs' - {g})"] Fs'_fin
                  by auto

                then show ?thesis using has_sup_subset[OF _ F_fs'_sup'(2) Sub, of "z1"] Fs'_fin
                  by auto

              qed
            qed
          qed

          have Diff_combine : "((Fs' - {g}) \<union> (Fs' - {f})) = Fs'"
            using False
            by(auto)


          have Fs'_combine : "((\<lambda>f. f syn supr) ` (Fs' - {g}) \<union> (\<lambda>f. f syn supr) ` (Fs' - {f})) = 
            ((\<lambda> f . f syn supr) ` Fs')"
            unfolding sym[OF image_Un] Diff_combine
            by(auto)

  
          obtain sup1 where Conc1 : "is_sup ((\<lambda>f. f syn supr) ` (Fs'  - {g}) \<union> (\<lambda>f. f syn supr) ` ((Fs' - {f}))) sup1"
            using nwise_sups[OF _ _ F_fs'_sup'(1) G_fs'_sup'(1) Nwise1] Fs'_fin
            by(auto simp add: has_sup_def)

          then have Conc1' : "is_sup ((\<lambda> f . f syn supr) ` Fs') sup1"
            unfolding Fs'_combine
            by(auto)          

          have Scross_union :
            "\<And> F1 F2 B . scross F1 B \<union> scross F2 B = scross (F1 \<union> F2) (B)"
            by(auto simp add: scross_def)

          have Fs'_scross : "(scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs \<union> scross ((\<lambda>f. f syn) ` (Fs' - {f})) Xs) 
            = scross ((\<lambda> f . f syn) ` Fs') Xs"
            unfolding Scross_union sym[OF image_Un] Diff_combine
            by(auto simp add: scross_def)
  
          have Fin1 : "finite (scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs)"
            using scross_finite[OF _ Fin_Xs, of "((\<lambda>f. f syn) ` (Fs' - {g}))"] Fs'_fin
            by auto
  
          have Fin2 : "finite (scross ((\<lambda>f. f syn) ` (Fs' - {f})) Xs)"
            using scross_finite[OF _ Fin_Xs, of "((\<lambda>f. f syn) ` (Fs' - {f}))"] Fs'_fin
            by auto
   
          obtain sup2 where Conc2 : "is_sup ((scross ((\<lambda>f. f syn) ` (Fs' - {g})) Xs) \<union> (scross ((\<lambda>f. f syn) ` (Fs' - {f})) Xs)) sup2"
            using nwise_sups[OF Fin1 Fin2 F_fs'_sup'(2) G_fs'_sup'(2) Nwise2]
            by(auto simp add: has_sup_def)
  
          then have Conc2' : "is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) sup2"
            unfolding Fs'_scross
            by(auto)

          (*
            ok, so what can we say about valid-sets? 
            everything but prio: closed under increasing information content
            maybe we can extend pairwise-sups to pairwise-ok?
            if inner data inside prio has sups, then prio has pairwise ok sups
            then maybe we can use this to use prio here, since ok_S \<subseteq> S s
            
          *)

          have True using sup_union2[OF F_fs'_sup(1) G_fs'_sup(1)] (* , of "(\<lambda> f . f syn supr)"] *)

          have Gs_fs_sup1 : "is_sup {f_fs'_sup', g_fs'_sup'} sup1"
            using sup_union2[OF F_fs'_sup'(1) G_fs'_sup'(1) Conc1]
            by auto
  
          have Gs_fs_sup2 : "is_sup {f_fs'_sup', g_fs'_sup'} sup2"
            using sup_union2[OF F_fs'_sup'(2) G_fs'_sup'(2) Conc2]
            by auto
  
          have Eq :"sup1 = sup2"
            using is_sup_unique[OF Gs_fs_sup1 Gs_fs_sup2]
            by auto

(* YOU ARE HERE *)
(* all that remains is to deal with this pesky set membership predicate... *)
          have True using F_fs'_sup
          have Conc3 : "sup1 \<in> S syn"
            using F_fs'_sup'(3) sups_pres
          

          show ?thesis
            using Conc1' Conc2' unfolding Eq 

(* now, we should be able to show these all are equal by using sup_union *)
          

        then show ?thesis using nwise_sups[OF _ _ F_fs'_sup(1) G_fs'_sup(1)]
nwise_sups[OF _ _ F_fs'_sup(2) G_fs'_sup(2)]
      qed
  
    then show ?case 

qed


(* next: want to show that, if for each lifting in a set of lifted functions,
 * a new lifted function is ortho. to all of them,
 * and they are sups_pres
 * then the entire thing is sups_pres.

* idea: we can do this using merge_l_ortho.
*)


(* all syntax? or can we do a specific s? *)
(* what do we need sups_pres for here, then?
i guess just maybe showing the validity?
*)
(*
lemma sups_pres_merge_lift :
  assumes H : " sups_pres {LMap l1 f1, LMap l2 f2} (\<lambda> s . S1 s \<inter> S2 s)"
  assumes Hx : "x \<in> S1 s \<inter> S2 s"
  shows "LMap (merge_l l1 l2) (f1, f2) s x = pcomps [LMap l1 f1, LMap l2 f2] s x"
proof-

  have H' : "sups_pres (set [LMap l1 f1, LMap l2 f2]) (\<lambda> s . S1 s \<inter> S2 s)"
    using H by auto

  have Sup: "is_sup (scross ((\<lambda>f. f s) ` set [LMap l1 f1, LMap l2 f2]) {x})
   (pcomps [LMap l1 f1, LMap l2 f2] s x)"
    using sups_pres_pcomps_gen1[OF H', where
f = "LMap l1 f1",
where Xs = "{x}",
where x = x,
where syn = s,
where xsup = x
(*  *)]
    using Hx
    using sup_singleton[of x]
    by(auto)
    
  show "LMap (merge_l l1 l2) (f1, f2) s x = pcomps [LMap l1 f1, LMap l2 f2] s x"
    apply(simp add: merge_l_def)
*)

end