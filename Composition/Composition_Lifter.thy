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
  assumes H : "l_ortho l1 S1 l2 S2"
  assumes H1 : "lifting_valid_presonly l1 S1"
  assumes H2 : "lifting_valid_presonly l2 S2"
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

  interpret LV1: lifting_valid_presonly l1 S1
    using H1 .

  interpret LV2: lifting_valid_presonly l2 S2
    using H2 .

  interpret Ortho: l_ortho l1 S1 l2 S2
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

    obtain res_sup where Res_sup :
      "is_sup {(lift_map_s id l1 f1 syn sup1), (lift_map_s id l2 f2 syn sup1)} res_sup"
      using Ortho.compat unfolding lift_map_s_def LMap_def has_sup_def
      by(fastforce)

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

    have Result_In :
      "[^ lift_map_s id l1 f1 syn sup1, lift_map_s id l2 f2 syn sup1 ^] \<in> S1 syn \<inter> S2 syn"
      using Ortho.compat_S[OF Conc1[unfolded lift_map_s_def LMap_def]]
      by(auto simp add: lift_map_s_def)

    show ?thesis using Conc1 Conc2 Result_In unfolding L1_2 lift_map_s_def LMap_def
      using H''
      by(auto simp add:scross_def)
  qed
qed

lemma merge_lift_pcomps : 
  shows "LMap (merge_l l1 l2) (f1, f2) s x = pcomps [LMap l1 f1, LMap l2 f2] s x"
  by(auto simp add: merge_l_def)


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