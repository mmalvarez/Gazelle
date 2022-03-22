theory Lift_Option
  imports "../Lifter"
begin

(*
 * option
 *)
text_raw \<open>%Snippet gazelle__lifter__instances__lift_option__option_l\<close>
definition option_l ::
  "('x, 'a, 'b) lifting \<Rightarrow> ('x, 'a, 'b option) lifting" where
"option_l t =
    LMake (\<lambda> s a b . 
              (case b of
                Some b' \<Rightarrow> Some (LUpd t s a b')
                | None \<Rightarrow> Some (LUpd t s a (LBase t s))))
            (\<lambda> s b . (case b of Some b' \<Rightarrow> LOut t s b'
                        | None \<Rightarrow> LOut t s (LBase t s)))
            (\<lambda> s . None)"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__lifter__instances__lift_option__option_l_S\<close>
definition option_l_S :: "('s, 'b) valid_set \<Rightarrow> ('s, 'b option) valid_set" where
"option_l_S S s = (Some ` S s)"
text_raw \<open>%EndSnippet\<close>

(* TODO: clean up mergeable instances so that we are consistently using Weakb instances
   where needed. *)
locale option_l_valid_weak = lifting_valid_weak

sublocale option_l_valid_weak \<subseteq> out : lifting_valid_weak "option_l l" "option_l_S S"
proof

  fix s a b
  show "LOut (option_l l) s (LUpd (option_l l) s a b) = a"
    using put_get 
    by(auto simp add:option_l_def split:option.splits)
next
  fix s b
  assume Hb : "b \<in> option_l_S S s"
  thus "b <[ LUpd (option_l l) s (LOut (option_l l) s b) b"
    using get_put_weak
    by(auto simp add:option_l_def option_l_S_def option_pleq split:option.splits)
next
  fix s :: 'a
  fix a
  fix b :: "'c option"
  show "LUpd (option_l l) s a b \<in> option_l_S S s"
    using put_S
    by(auto simp add: option_l_def option_l_S_def split:option.splits)
qed

lemma (in option_l_valid_weak) ax :
  shows "lifting_valid_weak (option_l l) (option_l_S S)"
  using out.lifting_valid_weak_axioms
    by auto

lemma (in option_l_valid_weak) ax_g :
  assumes "S' = option_l_S S"
  shows "lifting_valid_weak (option_l l) S'"
  using out.lifting_valid_weak_axioms assms
  by auto

locale option_l_valid_base_ext = lifting_sig

sublocale option_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "option_l l" "option_l_S S"
proof
  fix s
  show "LBase (option_l l) s = \<bottom>"
    by(auto simp add: option_l_def option_bot)
qed

lemma (in option_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (option_l l)"
  using out.lifting_valid_base_ext_axioms by auto

(*
locale option_l_valid_weak_base = option_l_valid_weak + option_l_valid_base_ext

sublocale option_l_valid_weak_base \<subseteq> out: lifting_valid_weak_base "option_l l" "option_l_S S"
proof
qed

lemma (in option_l_valid_weak_base) ax :
  shows "lifting_valid_weak_base (option_l l) (option_l_S S)"
  using out.lifting_valid_weak_base_axioms
    by auto

lemma (in option_l_valid_weak_base) ax_g :
  assumes "S' = option_l_S S"
  shows "lifting_valid_weak_base (option_l l) S'"
  using out.lifting_valid_weak_base_axioms assms
  by auto
*)

locale option_l_valid_ext = lifting_valid_ext

sublocale option_l_valid_ext \<subseteq> out : lifting_valid_ext "option_l l" "option_l_S S"
proof
  fix s a b
  (*assume "b \<in> option_l_S S s"*)
  show "b <[ LUpd (option_l l) s a b"
    using get_put
    by(auto simp add:option_l_def option_l_S_def LNew_def option_pleq split:option.splits)
qed

lemma (in option_l_valid_ext) ax :
  shows "lifting_valid_ext (option_l l)"
  using out.lifting_valid_ext_axioms
    by auto

locale option_l_valid_ok_ext = lifting_valid_ok_ext

sublocale option_l_valid_ok_ext \<subseteq> out: lifting_valid_ok_ext "option_l l" "option_l_S S"
proof
  fix s
  show "ok_S \<subseteq> option_l_S S s" using ok_S_valid
    by(auto simp add: option_l_S_def option_ok_S)
next
  fix s a b
  assume "(b :: 'c option) \<in> ok_S"
  then show "LUpd (option_l l) s a b \<in> ok_S"
    using ok_S_put
    by(auto simp add: option_l_S_def option_l_def option_ok_S split: option.splits)
qed

lemma (in option_l_valid_ok_ext) ax:
  shows "lifting_valid_ok_ext (option_l l) (option_l_S S)"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in option_l_valid_ok_ext) ax_g :
  assumes "S' = option_l_S S"
  shows "lifting_valid_ok_ext (option_l l) S'"
  using out.lifting_valid_ok_ext_axioms assms
  by auto


locale option_l_valid_pres_ext = lifting_valid_pres_ext + option_l_valid_weak

sublocale option_l_valid_pres_ext \<subseteq> out : lifting_valid_pres_ext "option_l l" "option_l_S S"
proof
  fix V
  fix s 
  fix v supr :: "'c option"
  fix f

  assume Nemp : "v \<in> V"
  assume V_valid : "V \<subseteq> option_l_S S s"

  assume Hsup : "is_sup V supr"
  assume Hsup_in : "supr \<in> option_l_S S s"

  obtain supr' where Supr' : "supr = Some supr'" "supr' \<in> S s"
    using V_valid Hsup_in by(auto simp add: option_l_S_def)

  show "is_sup (LMap (option_l l) f s ` V) (LMap (option_l l) f s supr)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (option_l l) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (option_l l) f s xo = x"
      by auto

    have "xo <[ supr" using is_supD1[OF Hsup Xo(1)] by simp

    have "x \<in> option_l_S S s"
      using put_S Xo
      by(auto simp add: option_l_S_def option_l_def split: option.splits)

    then obtain x' where X' : "x = Some x'" "x' \<in> S s"
      by(auto simp add: option_l_S_def)

    obtain xo' where Xo' : "xo = Some xo'" "xo' \<in> S s" using V_valid Xo
      by(auto simp add: option_l_S_def)

    have "xo' <[ supr'" using Xo' Supr' `xo <[ supr`
      by(simp add: option_pleq)

    hence "is_sup {xo', supr'} supr'"
      using is_sup_pair by auto

    hence Conc' : "is_sup (LMap l f s ` {xo', supr'}) (LMap l f s supr')"
      using Xo' Supr' pres[of xo' "{xo', supr'}" s supr' f] 
      by auto

    thus "x <[ LMap (option_l l) f s supr"
      using is_supD1[OF Conc', of x'] X' Xo Xo' Supr'
      by(cases l; auto simp add: option_l_def option_pleq)
  next

    fix z

    assume Ub : "is_ub (LMap (option_l l) f s ` V) z" 

    obtain V' where SV' : "V = Some ` V'" "V' \<subseteq> S s"
      using V_valid
      by(auto simp add: option_l_S_def; blast)

    obtain v' where V' : "v = Some v'" "v' \<in> V'"
      using Nemp SV'
      by auto

    have Supr'_sup : "is_sup V' supr'"
    proof(rule is_supI)
      fix x'

      assume "x' \<in> V'"

      then show "x' <[ supr'"
        using is_supD1[OF Hsup, of "Some x'"] Supr' SV' V'
        by(auto simp add: option_pleq)
    next

      fix z'

      assume "is_ub V' z'"

      then have "is_ub V (Some z')"
        using V' SV'
        by(auto simp add: option_pleq is_ub_def)

      then show "supr' <[ z'"
        using is_supD2[OF Hsup, of "Some z'"] Supr'
        by(auto simp add: option_pleq)
    qed

    have Supr'_sup : "is_sup (LMap l f s ` V') (LMap l f s supr')"
      using pres[OF V'(2) SV'(2) Supr'_sup, of f] Supr'(2)
      by auto

    obtain vr' where Vr' : "LMap (option_l l) f s v = Some vr'"
      using put_get V'
      by(cases l; auto simp add: option_l_def)

    have "LMap (option_l l) f s v <[ z"
      using is_ubE[OF Ub, of "LMap (option_l l) f s v"] Nemp
      by(auto)

    then obtain z' where Z' : "z = Some z'" using Vr'
      by(cases z; auto simp add: option_pleq)

    hence "is_ub (LMap l f s ` V') z'"
      using Ub SV'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)

    hence "LMap l f s supr' <[ z'"
      using is_supD2[OF Supr'_sup] by auto

    then show "LMap (option_l l) f s supr <[ z" using V' Z' Supr'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)
  qed
qed

lemma (in option_l_valid_pres_ext) ax:
  shows "lifting_valid_pres_ext (option_l l) (option_l_S S)"
  using out.lifting_valid_pres_ext_axioms
  by auto

lemma (in option_l_valid_pres_ext) ax_g :
  assumes "S' = option_l_S S"
  shows "lifting_valid_pres_ext (option_l l) S'"
  using out.lifting_valid_pres_ext_axioms assms
  by auto

locale option_l_valid_base_pres_ext = option_l_valid_pres_ext

sublocale option_l_valid_base_pres_ext \<subseteq> out: lifting_valid_base_pres_ext "option_l l" "option_l_S S"
proof
  show "\<And> s . \<bottom> \<notin> option_l_S S s"
    by(auto simp add: option_l_S_def option_bot)
qed

lemma (in option_l_valid_base_pres_ext) ax :
  shows "lifting_valid_base_pres_ext (option_l l) (option_l_S S)"
  using out.lifting_valid_base_pres_ext_axioms
  by auto

lemma (in option_l_valid_base_pres_ext) ax_g :
  assumes "S' = option_l_S S"
  shows "lifting_valid_base_pres_ext (option_l l) S'"
  using out.lifting_valid_base_pres_ext_axioms assms
  by auto
  

locale option_l_valid_pairwise_ext = 
  lifting_valid_pairwise_ext

sublocale option_l_valid_pairwise_ext \<subseteq> out : lifting_valid_pairwise_ext "option_l_S S"
proof
  fix s
  fix x1 x2 x3 s12 s13 s23 s123 :: "'b option"
  assume X1 : "x1 \<in> option_l_S S s"
  assume X2 :"x2 \<in> option_l_S S s"
  assume X3 : "x3 \<in> option_l_S S s"
  assume S12 :"is_sup {x1, x2} s12"
  assume S12_in :"s12 \<in> option_l_S S s"
  assume S23 :"is_sup {x2, x3} s23"
  assume S23_in :"s23 \<in> option_l_S S s"
  assume S13 :"is_sup {x1, x3} s13" 
  assume S13_in :"s13 \<in> option_l_S S s"  
  assume S123 :"is_sup {x1, x2, x3} s123"

  obtain x1' where X1' : "x1 = Some x1'" "x1' \<in> S s"
    using X1
    by(auto simp add: option_l_S_def)

  obtain x2' where X2' : "x2 = Some x2'" "x2' \<in> S s"
    using X2
    by(auto simp add: option_l_S_def)

  obtain x3' where X3' : "x3 = Some x3'" "x3' \<in> S s"
    using X3
    by(auto simp add: option_l_S_def)

  obtain s12' where S12' : "s12 = Some s12'"  "s12' \<in> S s"
    using S12_in
    by(auto simp add: option_l_S_def)

  obtain s13' where S13' : "s13 = Some s13'" "s13' \<in> S s"
    using S13_in
    by(auto simp add: option_l_S_def)

  obtain s23' where S23' : "s23 = Some s23'" "s23' \<in> S s"
    using S23_in
    by(auto simp add: option_l_S_def)

  have S12'_sup : "is_sup {x1', x2'} s12'"
    using is_sup_Some'[of x1' "{x1', x2'}" s12'] S12
    unfolding S12' X1' X2'
    by auto

  have S13'_sup : "is_sup {x1', x3'} s13'"
    using is_sup_Some'[of x1' "{x1', x3'}" s13'] S13
    unfolding S13' X1' X3'
    by auto

  have S23'_sup : "is_sup {x2', x3'} s23'"
    using is_sup_Some'[of x2' "{x2', x3'}" s23'] S23
    unfolding S23' X2' X3'
    by auto

  obtain s123' where S123' : "s123 = Some s123'"
    using is_supD1[OF S123, of x1]
    unfolding X1'
    by(cases s123; auto simp add: option_pleq)

  have S123'_sup : "is_sup {x1', x2', x3'} s123'"
    using is_sup_Some'[of x1' "{x1', x2', x3'}" s123'] S123
    unfolding X1' X2' X3' S123'
    by auto

  have "s123' \<in> S s"
    using pairwise_S[OF X1'(2) X2'(2) X3'(2) S12'_sup S12'(2) S23'_sup S23'(2) S13'_sup S13'(2) S123'_sup ]
    by auto

  then show " s123 \<in> option_l_S S s"
    using S123'
    by(auto simp add: option_l_S_def)
qed


lemma (in option_l_valid_pairwise_ext) ax :
  shows "lifting_valid_pairwise_ext (option_l_S S)"
  using out.lifting_valid_pairwise_ext_axioms
  by auto

lemma (in option_l_valid_pairwise_ext) ax_g :
  assumes "S' = option_l_S S"
  shows "lifting_valid_pairwise_ext S'"
  using out.lifting_valid_pairwise_ext_axioms assms
  by auto

locale option_l_ortho =
  l_ortho

sublocale option_l_ortho \<subseteq> out : l_ortho "option_l l1"  "option_l_S S1" "option_l l2" "option_l_S S2"
proof
  fix s
  show "LBase (option_l l1) s = LBase (option_l l2) s"
    by(auto simp add: option_l_def)
next

  fix b s 
  fix a1 :: 'b
  fix a2 :: 'd

  have Base: "LBase l1 s = LBase l2 s"
    using eq_base by auto

  show "LUpd (option_l l1) s a1 (LUpd (option_l l2) s a2 b) =
       LUpd (option_l l2) s a2 (LUpd (option_l l1) s a1 b)"
  proof(cases b)
    case None

    then show ?thesis
      using compat[of s a1 a2 "LBase l1 s"] eq_base
      by(auto simp add: option_l_def)
  next
    case (Some b')

    then show ?thesis
      using compat
      by(auto simp add: option_l_def)
  qed
next

  fix b s a1
  show "LOut (option_l l2) s (LUpd (option_l l1) s a1 b) = LOut (option_l l2) s b"
    using eq_base put1_get2
    by(cases b; auto simp add: option_l_def)
next
  fix b s a2
  show "LOut (option_l l1) s (LUpd (option_l l2) s a2 b) =
       LOut (option_l l1) s b"
    using eq_base put2_get1
    by(cases b; auto simp add: option_l_def)
next
  fix b s a1

  assume B: "b \<in> option_l_S S2 s"

  then obtain b' where B' : "b = Some b'" "b' \<in> S2 s"
    by(auto simp add: option_l_S_def)

  have "Some (LUpd l1 s a1 b') \<in> Some ` S2 s"
    using put1_S2[OF B'(2)]
    by auto

  then show "LUpd (option_l l1) s a1 b \<in> option_l_S S2 s"
    using B'
    by(auto simp add: option_l_S_def option_l_def)
next
  fix b s a2
  assume B: "b \<in> option_l_S S1 s"

  then obtain b' where B' : "b = Some b'" "b' \<in> S1 s"
    by(auto simp add: option_l_S_def)

  have "Some (LUpd l2 s a2 b') \<in> Some ` S1 s"
    using put2_S1[OF B'(2)]
    by auto

  then show "LUpd (option_l l2) s a2 b \<in> option_l_S S1 s"
    using B'
    by(auto simp add: option_l_S_def option_l_def)
qed

lemma (in option_l_ortho) ax :
  shows "l_ortho (option_l l1)  (option_l_S S1) (option_l l2) (option_l_S S2)"
  using out.l_ortho_axioms
  by auto

lemma (in option_l_ortho) ax_g :
  assumes H1 : "\<And> x . S'1 x = option_l_S S1 x"
  assumes H2 : "\<And> x . S'2 x = option_l_S S2 x"
  shows "l_ortho (option_l l1) S'1 (option_l l2) S'2"
proof-
  have H1' : "S'1 = option_l_S S1"
    using H1 by auto

  have H2' : "S'2 = option_l_S S2"
    using H2 by auto

  show ?thesis using ax unfolding H1' H2'
    by auto
qed

lemma sup_singleton :
  "is_sup {x} x"
  by(auto simp add: is_least_def is_ub_def is_sup_def leq_refl)

locale option_l_ortho_base_ext = l_ortho_base_ext

sublocale option_l_ortho_base_ext \<subseteq> out : l_ortho_base_ext "option_l l1" "option_l l2"
proof
  fix s

  show "LBase (option_l l1) s = \<bottom>"
    by(auto simp add: option_l_def option_bot)
next

  fix s
  show "LBase (option_l l2) s = \<bottom>"
    by(auto simp add: option_l_def option_bot)
qed

lemma (in option_l_ortho_base_ext) ax :
  shows "l_ortho_base_ext (option_l l1) (option_l l2)"
  using out.l_ortho_base_ext_axioms
  by auto


(* NB we are not currenly using l_ortho_pres *)
(*
locale option_l_ortho_pres = option_l_ortho + l_ortho_pres + l_ortho_base

sublocale option_l_ortho_pres \<subseteq> out : l_ortho_pres "option_l l1" "option_l_S S1" "option_l l2" "option_l_S S2"
proof
  fix s f1 f2 s1 s2 v V

  assume Sup1 : "is_sup (LMap (option_l l1) f1 s ` V) s1"
  assume Sup2 : "is_sup (LMap (option_l l2) f2 s ` V) s2"
  assume Vin : "v \<in> V"
  assume Vsub1 : "V \<subseteq> option_l_S S1 s"
  assume Sin1 : "s1 \<in> option_l_S S1 s \<inter> option_l_S S2 s"
  assume Vsub2 : "V \<subseteq> option_l_S S2 s"
  assume Sin2 : "s2 \<in> option_l_S S1 s \<inter> option_l_S S2 s"

  obtain V' where SV' : "V' = { x' . Some x' \<in> V}"
    by auto

  have Vv' : "V = Some ` V'"
    using Vsub1 SV'
    by(auto simp add: option_l_S_def)

  have V'sub1 : "V' \<subseteq> S1 s"
    using Vv' Vsub1
    by(auto simp add: option_l_S_def)

  have V'sub2 : "V' \<subseteq> S2 s"
    using Vv' Vsub2
    by(auto simp add: option_l_S_def)

  obtain v' where V' :
    "v' \<in> V'" "v = Some v'"
    using Vin
    unfolding Vv'
    by auto

  have Some_map1 : "LMap (option_l l1) f1 s `V = Some ` LMap l1 f1 s ` V'"
  proof
    show "LMap (option_l l1) f1 s ` V \<subseteq> Some ` LMap l1 f1 s ` V'"
      using Vv'
      by(auto simp add: option_l_def)
  next
    show "Some ` LMap l1 f1 s ` V' \<subseteq> LMap (option_l l1) f1 s ` V"
    proof
      fix x

      assume X: "x \<in> Some ` LMap l1 f1 s ` V'"

      then obtain xo where Xo : "xo \<in> V'" "x = Some (LMap l1 f1 s xo)"
        by auto

      then have X_eq : "x = LMap (option_l l1) f1 s (Some xo)"
        by(auto simp add: option_l_def)

      have Xo_in : "Some xo \<in> V"
        using Xo Vv' by auto

      then show "x \<in> LMap (option_l l1) f1 s ` V"
        using imageI[OF Xo_in, of "LMap (option_l l1) f1 s"] Xo
        by(auto simp add: option_l_def)
    
    qed
  qed

  have Some_map2 : "LMap (option_l l2) f2 s `V = Some ` LMap l2 f2 s ` V'"
  proof
    show "LMap (option_l l2) f2 s ` V \<subseteq> Some ` LMap l2 f2 s ` V'"
      using Vv'
      by(auto simp add: option_l_def)
  next
    show "Some ` LMap l2 f2 s ` V' \<subseteq> LMap (option_l l2) f2 s ` V"
    proof
      fix x

      assume X: "x \<in> Some ` LMap l2 f2 s ` V'"

      then obtain xo where Xo : "xo \<in> V'" "x = Some (LMap l2 f2 s xo)"
        by auto

      then have X_eq : "x = LMap (option_l l2) f2 s (Some xo)"
        by(auto simp add: option_l_def)

      have Xo_in : "Some xo \<in> V"
        using Xo Vv' by auto

      then show "x \<in> LMap (option_l l2) f2 s ` V"
        using imageI[OF Xo_in, of "LMap (option_l l2) f2 s"] Xo
        by(auto simp add: option_l_def)
    qed
  qed

  have Some_map3 : "LMap (option_l l1) f1 s ` Some ` LMap l2 f2 s ` V' = Some ` LMap l1 f1 s ` LMap l2 f2 s ` V'"
  proof
    show "LMap (option_l l1) f1 s ` Some ` LMap l2 f2 s ` V'
      \<subseteq> Some ` LMap l1 f1 s ` LMap l2 f2 s ` V'"
      using Vv'
      by(auto simp add: option_l_def)
  next
    show "Some ` LMap l1 f1 s ` LMap l2 f2 s ` V'
      \<subseteq> LMap (option_l l1) f1 s ` Some ` LMap l2 f2 s ` V'"
    proof
      fix x
      assume X: "x \<in> Some ` LMap l1 f1 s ` LMap l2 f2 s ` V'"

      then obtain xo where Xo : "xo \<in> V'" "x = Some (LMap l1 f1 s (LMap l2 f2 s xo))"
        by auto

      then have X_eq : "x = LMap (option_l l1) f1 s (Some (LMap l2 f2 s xo))"
        using Vv'
        by(auto simp add: option_l_def)

      have Xo_in : "Some xo \<in> V"
        using Xo Vv' by auto

      have Xo_in' : "Some (LMap l2 f2 s xo) \<in> Some ` LMap l2 f2 s ` V'"
        using Xo
        by auto

      show "x \<in> LMap (option_l l1) f1 s ` Some ` LMap l2 f2 s ` V'"
        using imageI[OF Xo_in', of "LMap (option_l l1) f1 s"] X Xo
        by(auto simp add: option_l_def)
    qed
  qed

  show "is_sup
        (LMap (option_l l1) f1 s `
         LMap (option_l l2) f2 s ` V)
        (LMap (option_l l1) f1 s s2)"
  proof(cases s1)
    case None
    have "LMap (option_l l1) f1 s v <[ s1"
      using is_supD1[OF Sup1 imageI[OF Vin]]
      by(auto)

    then have False using None
      by(cases v; auto simp add: option_l_def option_pleq)

    then show ?thesis by auto
  next
    case (Some s1')

    show ?thesis
    proof(cases s2)
      case None' : None

      have "LMap (option_l l2) f2 s v <[ s2"
        using is_supD1[OF Sup2 imageI[OF Vin]]
        by(auto)

      then have False using None'
        by(cases v; auto simp add: option_l_def option_pleq)

      then show ?thesis by auto
    next
      case Some' : (Some s2')

      have Sup'1 : "is_sup (LMap l1 f1 s ` V') s1'"
      proof(rule is_supI)
        fix x
        assume X : "x \<in> LMap l1 f1 s ` V'"

        then obtain x' where X' : "x' \<in> V'" "LMap l1 f1 s x' = x"
          by auto

        have "Some x \<in> LMap (option_l l1) f1 s ` V"
          unfolding Some_map1
          using imageI[OF X, of Some]
          by(auto simp add: option_l_def)

        then show "x <[ s1'"
          using is_supD1[OF Sup1, of "Some x"] Some
          by(auto simp add: option_pleq)
      next
        fix w

        assume Ub : "is_ub (LMap l1 f1 s ` V') w"
        have Ub' : "is_ub (LMap (option_l l1) f1 s ` V) (Some w)"
        proof(rule is_ubI)
          fix z
          assume Z: "z \<in> LMap (option_l l1) f1 s ` V"

          then have "z \<in> Some ` LMap l1 f1 s ` V'"
            unfolding Some_map1
            by auto

          then obtain z' where Z' : "z' \<in> LMap l1 f1 s ` V'" "z = Some z'"
            by auto

          show "z <[ Some w"
            using is_ubE[OF Ub Z'(1)] Z'(2)
            by(auto simp add: option_pleq)
        qed

        show "s1' <[ w"
          using is_supD2[OF Sup1 Ub'] Some
          by(auto simp add: option_pleq)
      qed

      have Sup'2 : "is_sup (LMap l2 f2 s ` V') s2'"
      proof(rule is_supI)
        fix x
        assume X : "x \<in> LMap l2 f2 s ` V'"

        then obtain x' where X' : "x' \<in> V'" "LMap l2 f2 s x' = x"
          by auto

        have "Some x \<in> LMap (option_l l2) f2 s ` V"
          unfolding Some_map2
          using imageI[OF X, of Some]
          by(auto simp add: option_l_def)

        then show "x <[ s2'"
          using is_supD1[OF Sup2, of "Some x"] Some'
          by(auto simp add: option_pleq)
      next
        fix w

        assume Ub : "is_ub (LMap l2 f2 s ` V') w"
        have Ub' : "is_ub (LMap (option_l l2) f2 s ` V) (Some w)"
        proof(rule is_ubI)
          fix z
          assume Z: "z \<in> LMap (option_l l2) f2 s ` V"

          then have "z \<in> Some ` LMap l2 f2 s ` V'"
            unfolding Some_map2
            by auto

          then obtain z' where Z' : "z' \<in> LMap l2 f2 s ` V'" "z = Some z'"
            by auto

          show "z <[ Some w"
            using is_ubE[OF Ub Z'(1)] Z'(2)
            by(auto simp add: option_pleq)
        qed

        show "s2' <[ w"
          using is_supD2[OF Sup2 Ub'] Some'
          by(auto simp add: option_pleq)
      qed

      have Sin1' : "s1' \<in> S1 s \<inter> S2 s"
        using Sin1 Some
        by(auto simp add: option_l_S_def)

      have Sin2' : "s2' \<in> S1 s \<inter> S2 s"
        using Sin2 Some'
        by(auto simp add: option_l_S_def)

      have Conc' : "is_sup (LMap l1 f1 s ` LMap l2 f2 s ` V') (LMap l1 f1 s s2')"
        using compat_pres1[OF V'(1) V'sub1 V'sub2 Sup'1 Sin1' Sup'2 Sin2']
        by auto

      show "is_sup
          (LMap (option_l l1) f1 s ` LMap (option_l l2) f2 s ` V)
          (LMap (option_l l1) f1 s s2)"
      proof(rule is_supI)
        fix z

        assume Z: "z \<in> LMap (option_l l1) f1 s `
             LMap (option_l l2) f2 s ` V "

        then have Z1 : "z \<in> LMap (option_l l1) f1 s `
             (Some ` LMap l2 f2 s ` V')"
          using Some_map2
          by auto

        then obtain z' where Z2 : "z = Some z'" "z' \<in> LMap l1 f1 s ` LMap l2 f2 s ` V'"
          unfolding Some_map3
          by auto

        show "z <[ LMap (option_l l1) f1 s s2"
          using is_supD1[OF Conc' Z2(2)] Some' Z2(1)
          by(auto simp add: option_l_def option_pleq)
      next

        fix w

        assume Ub : "is_ub
           (LMap (option_l l1) f1 s ` LMap (option_l l2) f2 s ` V)
           w"

        then have Ub1 : "is_ub (LMap (option_l l1) f1 s `
             (Some ` LMap l2 f2 s ` V')) w"
          using Some_map2
          by auto

        show "LMap (option_l l1) f1 s s2 <[ w"
        proof(cases w)
          case None'' : None

          have In' : "LMap (option_l l1) f1 s (Some (LMap l2 f2 s v')) \<in> LMap (option_l l1) f1 s ` Some ` LMap l2 f2 s ` V' "
            using imageI[OF V'(1), of "LMap (option_l l1) f1 s o Some o LMap l2 f2 s"]
            by auto

          have False using is_ubE[OF Ub1 In'] None''
            by(auto simp add: option_l_def option_pleq)

          then show ?thesis by auto
        next
          case Some'' : (Some w')
          have Ub2 : "is_ub (LMap l1 f1 s ` LMap l2 f2 s ` V') w'"
          proof(rule is_ubI)
            fix k

            assume K: "k \<in> LMap l1 f1 s ` LMap l2 f2 s ` V'"

            then have K' : "Some k \<in> Some ` LMap l1 f1 s ` LMap l2 f2 s ` V'"
              by auto

            show "k <[ w'"
              using is_ubE[OF Ub1, of "Some k"] Some'' K'
              unfolding Some_map3
              by(auto simp add: option_pleq)
          qed
          
          show ?thesis 
            using is_supD2[OF Conc' Ub2] Some'' Some'
            by(auto simp add: option_l_def option_pleq)
        qed
      qed
    qed
  qed
*)


locale option_l_ortho_ok_ext =
  option_l_ortho + l_ortho_ok_ext

sublocale option_l_ortho_ok_ext \<subseteq> out : l_ortho_ok_ext "option_l l1" "option_l l2" .

locale option_l_valid_oc_ext =
  lifting_valid_oc_ext

sublocale option_l_valid_oc_ext \<subseteq> out : lifting_valid_oc_ext "option_l l" "option_l_S S"
proof
  fix Xs :: "('c :: Pord_Weak) option set"
  fix supr :: "'c option" 
  fix s :: 'a
  fix r :: 'b
  fix w :: "'c option"
  assume W: "w \<in> Xs"
  assume Supr : "is_sup Xs supr"
  assume Compat :
    "(\<And>x. x \<in> Xs \<Longrightarrow>
             LOut (option_l l) s x = r)"



  show "LOut (option_l l) s supr = r"
  proof(cases supr)
    case None

    then have "w = None"
      using is_supD1[OF Supr W]
      by(cases w; auto simp add: option_pleq)

    then have "r = LOut l s (LBase l s)"
      using Compat[OF W]
      by(auto simp add: option_l_def)

    then show ?thesis using None
      by(auto simp add: option_l_def)
  next
    case (Some supr')

    show ?thesis
    proof(cases "Xs = {None}")
      case True

      have Ub' : "is_ub {None} None"
        by(auto simp add: is_ub_def leq_refl)

      then have False using is_supD2[OF Supr[unfolded True] Ub'] True Some
        by(auto simp add: option_pleq)

      then show ?thesis by auto
    next
      case False

      show ?thesis
      proof(cases "\<exists> y . y \<in> Xs \<and> y \<noteq> None")
        case Y_false : False

        then have "Xs = {}" using False
          by(auto)

        then have False using W by auto

        then show ?thesis by auto
      next
        case Y_true : True

        then obtain y' where Y' : "Some y' \<in> Xs"
          by auto

        obtain Xs' where Xs' : "Xs' = {x . (Some x \<in> Xs)}"
          by simp

        then have Y'_in : "y' \<in> Xs'" using Y' by auto

        have Sup_some : "is_sup (Some ` Xs') (Some supr')"
        proof(rule is_supI)
          fix x
          assume "x \<in> Some ` Xs'"

          then have X_orig : "x \<in> Xs"
            using Xs'
            by auto

          show "x <[ Some supr'"
            using is_supD1[OF Supr X_orig] Some
            by auto
        next
          fix x'
          assume Ub: "is_ub (Some ` Xs') x'"

          have Ub' : "is_ub Xs x'"
          proof(rule is_ubI)
            fix z
            assume Z: "z \<in> Xs"

            show "z <[ x'"
            proof(cases z)
              case None' : None
              then show "z <[ x'"
                by(auto simp add: option_pleq)
            next
              case Some' : (Some z')

              then have Z'_in1 : "z' \<in> Xs'"
                using Xs' Z
                by(auto)

              then have Z'_in2 : "Some z' \<in> (Some ` Xs')"
                by auto

              then show ?thesis using is_ubE[OF Ub Z'_in2] Some'
                by auto
            qed
          qed

          show "Some supr' <[ x'"
            using is_supD2[OF Supr Ub']
              Some
            by auto
        qed

        then have Sup_xs' : "is_sup Xs' supr'"
          using is_sup_Some'[OF Y'_in Sup_some]
          by auto

        have Xs'_compat :
          "(\<And>x. x \<in> Xs' \<Longrightarrow> LOut l s x = r)"
        proof-
          fix k
          assume K : "k \<in> Xs'"

          then have K1 : "Some k \<in> Xs"
            using Xs'
            by auto

          show "LOut l s k = r"
            using Compat[OF K1]
            by(auto simp add: option_l_def)
        qed
          
        show "LOut (option_l l) s supr = r"
          using output_consistent[OF Y'_in Sup_xs' Xs'_compat]
            Some
          by(auto simp add: option_l_def)
      qed
    qed
  qed
qed

lemma (in option_l_valid_oc_ext) ax :
  shows "lifting_valid_oc_ext (option_l l)"
  using out.lifting_valid_oc_ext_axioms
  by auto

end