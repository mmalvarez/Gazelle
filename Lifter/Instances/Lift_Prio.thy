theory Lift_Prio
  imports "../Lifter"
begin

(*
 * prio
 *)
definition prio_l ::
 "('x \<Rightarrow> nat) \<Rightarrow>
  ('x \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
  ('x, 'a, 'b) lifting\<Rightarrow>
  ('x, 'a, 'b md_prio) lifting" where
"prio_l f0 f1 t =
      LMake (\<lambda> s a b . (case b of
                             mdp m b' \<Rightarrow> mdp (f1 s m) (LUpd t s a b')))
            (\<lambda> s p . (case p of
                       mdp m b \<Rightarrow> LOut t s b))
            (\<lambda> s . mdp (f0 s) (LBase t s))"

definition prio_l_S :: "('x, 'b) valid_set \<Rightarrow> ('x, 'b md_prio) valid_set" where
"prio_l_S S s =
  { p . (case p of
          mdp n x \<Rightarrow> x \<in> S s) }"

locale prio_l_valid_weak' =
  fixes l :: "('syn, 'a, 'b) lifting"
  fixes f0 :: "'syn \<Rightarrow> nat"
  fixes f1 :: "'syn \<Rightarrow> nat \<Rightarrow> nat"
  assumes f1_nondecrease : "\<And> s p . p \<le> f1 s p"


locale prio_l_valid_weak = prio_l_valid_weak' + lifting_valid_weak

sublocale prio_l_valid_weak \<subseteq> out : lifting_valid_weak "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a b
  show "LOut (prio_l f0 f1 l) s (LUpd (prio_l f0 f1 l) s a b) = a"
    using put_get
    by(auto simp add:prio_l_def LNew_def split:md_prio.splits)
next
  fix s b
  assume Hb : "b \<in> prio_l_S S s"
  show "b <[ LUpd (prio_l f0 f1 l) s (LOut (prio_l f0 f1 l) s b) b"
    using get_put_weak f1_nondecrease Hb
    by(auto simp add:prio_l_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s a b
  show "LUpd (prio_l f0 f1 l) s a b \<in> prio_l_S S s"
    using put_S
    by(auto simp add: prio_l_def prio_l_S_def LNew_def split:md_prio.splits)
qed

lemma (in prio_l_valid_weak) ax :
  shows "lifting_valid_weak (prio_l f0 f1 l) (prio_l_S S)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in prio_l_valid_weak) ax_g :
  assumes "S' = prio_l_S S"
  shows "lifting_valid_weak (prio_l f0 f1 l) S'"
  using out.lifting_valid_weak_axioms assms
  by auto

locale prio_l_valid_ext = lifting_valid_ext + prio_l_valid_weak'

sublocale prio_l_valid_ext \<subseteq> out : lifting_valid_ext "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a
  fix b :: "'c md_prio"
  obtain b' pb'  where B' : "b = mdp pb' b'"
    by(cases b; auto)

  show "b <[ LUpd (prio_l f0 f1 l) s a b"
    using get_put B' f1_nondecrease
    by(auto simp add: prio_l_def prio_pleq)
qed

lemma (in prio_l_valid_ext) ax :
  shows "lifting_valid_ext (prio_l f0 f1 l) "
  using out.lifting_valid_ext_axioms
  by auto

locale prio_l_valid_ext_strong' =
  fixes l :: "('syn, 'a, ('b :: Pord_Weak)) lifting"
  fixes S :: "'syn \<Rightarrow> 'b set"
  fixes f0 :: "'syn \<Rightarrow> nat"
  fixes f1 :: "'syn \<Rightarrow> nat \<Rightarrow> nat"
  assumes f1_increase : "\<And> s p . p < f1 s p"

locale prio_l_valid_ext_strong = prio_l_valid_ext_strong'

sublocale prio_l_valid_ext_strong \<subseteq> out : lifting_valid_ext "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a 
  fix b :: "'c md_prio"
(*  assume H: "b \<in> prio_l_S S s"*)
  obtain x1 p where B : "b = mdp p x1" by(cases b; auto)

  show " b <[ LUpd (prio_l f0 f1 l) s a b"
    using B f1_increase[of p s]
    by(auto simp add:prio_l_def LNew_def prio_pleq split:md_prio.splits)
qed

lemma (in prio_l_valid_ext_strong) ax :
  shows "lifting_valid_ext (prio_l f0 f1 l)"
  using out.lifting_valid_ext_axioms
  by auto

(* NB this is a weird case where we actually have to directly prove valid rather than doing
 * so componentwise. *)

locale prio_l_valid_strong = prio_l_valid_weak + prio_l_valid_ext_strong

lemma (in prio_l_valid_strong) ax :
  shows "lifting_valid (prio_l f0 f1 l) (prio_l_S S)"
  using out.lifting_valid_weak_axioms out.lifting_valid_ext_axioms
  by(intro_locales; auto)

lemma (in prio_l_valid_strong) ax_g :
  assumes H: "S' = prio_l_S S"
  shows "lifting_valid (prio_l f0 f1 l) S'"
  using ax assms
  by(auto)

locale prio_l_valid_ext_stronger' = prio_l_valid_ext_strong' +
  fixes T :: "('syn \<Rightarrow> ('b :: Pord_Weak) md_prio set)"
  assumes T : "\<And> x . prio_l_S S x \<subseteq> T x"

locale prio_l_valid_ext_stronger = prio_l_valid_strong + prio_l_valid_ext_stronger'
sublocale prio_l_valid_ext_stronger \<subseteq> out : lifting_valid "prio_l f0 f1 l" "T"
proof
  show "\<And>s b a. LOut (prio_l f0 f1 l) s (LUpd (prio_l f0 f1 l) s a b) = a"
    using out.put_get by auto
next
  fix s a b
  fix b :: "'c md_prio"

  obtain x1 p where B : "b = mdp p x1" by(cases b; auto)

  show "b <[ LUpd (prio_l f0 f1 l) s (LOut (prio_l f0 f1 l) s b) b"
    using f1_increase[of p s] B
    by(auto simp add:prio_l_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s a 
  fix b :: "('c md_prio)"

  obtain x1 x2 where B : "b = mdp x1 x2"
    by(cases b; auto)

  have Prio_in : "mdp (f1 s x1) (LUpd l s a x2) \<in> prio_l_S S s"
    using put_S
    by(auto simp add: prio_l_S_def)

  then have Prod_in' : "mdp (f1 s x1) (LUpd l s a x2) \<in> T s"
    using T[of s] by auto

  then show "LUpd (prio_l f0 f1 l) s a b \<in> T s" using B
    by(auto simp add: prio_l_def prio_l_S_def split: md_prio.splits)
qed

lemma (in prio_l_valid_ext_stronger) ax :
  shows "lifting_valid (prio_l f0 f1 l) T"
  using out.lifting_valid_weak_axioms out.lifting_valid_ext_axioms
  by(intro_locales; auto)

lemma (in prio_l_valid_ext_stronger) ax_g :
  assumes H: "S' = T"
  shows "lifting_valid (prio_l f0 f1 l) T"
  using ax assms
  by(auto)


locale prio_l_valid_base' =
  fixes l :: "('syn, 'a, ('b :: Pord_Weakb)) lifting"
  fixes S :: "('syn \<Rightarrow> 'b set)"
  fixes f0 :: "'syn \<Rightarrow> nat"
  assumes zero : "\<And> s . f0 s = 0"

locale prio_l_valid_base_ext = lifting_valid_base_ext + prio_l_valid_base'

sublocale prio_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s
  show "LBase (prio_l f0 f1 l) s = \<bottom>"
    using zero base
    by(auto simp add: prio_l_def prio_bot)
qed

lemma (in prio_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (prio_l f0 f1 l)"
  using out.lifting_valid_base_ext_axioms
  by auto

locale prio_l_valid_ok_ext = lifting_valid_ok_ext

locale prio_l_valid_weak_ok = prio_l_valid_weak + lifting_valid_weak_ok

sublocale prio_l_valid_ok_ext \<subseteq> out : lifting_valid_ok_ext "(prio_l f0 f1 l)" "(prio_l_S S)"
proof
  fix s
  show "ok_S \<subseteq> prio_l_S S s"
    using ok_S_valid[of s]
    by(auto simp add: prio_l_S_def prio_ok_S)
next
  fix s a
  fix b :: "'c md_prio"
  assume H: "b \<in> ok_S"

  obtain b' pb' where B' : "b = mdp pb' b'"
    by(cases b; auto)

  have H' : "b' \<in> ok_S"
    using H B'
    by(auto simp add: prio_l_S_def prio_ok_S)

  show "LUpd (prio_l f0 f1 l) s a b \<in> ok_S"
    using ok_S_put[OF H'] B'
    by(auto simp add: prio_l_S_def prio_l_def prio_ok_S)
qed

lemma (in prio_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (prio_l f0 f1 l) (prio_l_S S)"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in prio_l_valid_ok_ext) ax_g :
  assumes H : "S' = prio_l_S S"
  shows "lifting_valid_ok_ext (prio_l f0 f1 l) S'"
  using out.lifting_valid_ok_ext_axioms assms
  by auto

locale prio_l_valid_ext_stronger_ok = prio_l_valid_weak_ok + prio_l_valid_ext_stronger

sublocale prio_l_valid_ext_stronger_ok \<subseteq> out : lifting_valid_ok "prio_l f0 f1 l" "T"
proof
  fix s
  show "ok_S \<subseteq> T s"
    using T[of s] ok_S_valid[of s]
    by(fastforce simp add: prio_l_S_def prio_ok_S)
next
  fix s a
  fix b :: "'c md_prio"
  assume H: "b \<in> ok_S"

  obtain b' pb' where B' : "b = mdp pb' b'"
    by(cases b; auto)

  have H' : "b' \<in> ok_S"
    using H B'
    by(auto simp add: prio_l_S_def prio_ok_S)

  show "LUpd (prio_l f0 f1 l) s a b \<in> ok_S"
    using ok_S_put[OF H'] B'
    by(auto simp add: prio_l_S_def prio_l_def prio_ok_S)
qed

lemma (in prio_l_valid_ext_stronger_ok) ax :
  shows "lifting_valid_ok_ext (prio_l f0 f1 l) T"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in prio_l_valid_ext_stronger_ok) ax_g :
  assumes H : "S' = T"
  shows "lifting_valid_ok_ext (prio_l f0 f1 l) S'"
  using out.lifting_valid_ok_ext_axioms assms
  by auto


locale prio_l_valid_weak_ok_pres' =
  fixes l :: "('syn, 'a, ('b :: Pord)) lifting"
  fixes f0 :: "'syn \<Rightarrow> nat"
  fixes f1 :: "'syn \<Rightarrow> nat \<Rightarrow> nat"
  assumes f1_mono_leq : "\<And> s p1 p2 . p1 \<le> p2 \<Longrightarrow> f1 s p1 \<le> f1 s p2"
  assumes f1_mono_lt : "\<And> s p1 p2 . p1 < p2 \<Longrightarrow> f1 s p1 < f1 s p2"

locale prio_l_valid_base_pres = prio_l_valid_weak + prio_l_valid_base_ext + prio_l_valid_weak_ok_pres' + lifting_valid_pres_ext 


(* the way we proved this theorem, we actually need base for it to be true.
 * as well as strength. *)

locale prio_l_valid_base_ok_pres = prio_l_valid_weak_ok_pres' + prio_l_valid_weak + prio_l_valid_base_ext + prio_l_valid_ext + prio_l_valid_ok_ext + lifting_valid_base_ok_pres
sublocale prio_l_valid_base_ok_pres \<subseteq> out : lifting_valid_base_ok_pres "prio_l f0 f1 l" "prio_l_S S"
proof
(* TODO: this proof can almost definitely be drastically simplified. *)
  fix V
  fix s 
  fix v supr :: "'c md_prio"
  fix f

  assume Nemp : "v \<in> V"
  assume V_valid : "V \<subseteq> prio_l_S S s"

  assume Hsup : "is_sup V supr"
  assume Hsup_in : "supr \<in> prio_l_S S s"

  obtain supr' psupr' where Supr' : "supr = mdp psupr' supr'" "supr' \<in> S s"
    using V_valid Hsup_in
    by(auto simp add: prio_l_S_def split:md_prio.splits)

  have Vsubs : "V \<subseteq> ({ xp . (case xp of mdp p x \<Rightarrow> x \<in> S s)})"
    using V_valid
    by(auto simp add: prio_l_S_def)

  then obtain V' where SV' : "(\<lambda> x . case x of (mdp p m) \<Rightarrow> m) ` V = V'"
    by(blast)

  then have SV'_subs : "V' \<subseteq> S s"
    using V_valid
    by(auto simp add: prio_l_S_def split: md_prio.splits)

  obtain v' pv' where V' : "v = mdp pv' v'" "v' \<in> V'"
    using SV' imageI[OF Nemp, of "(\<lambda>x. case x of mdp p m \<Rightarrow> m)"]
    by(cases v; auto)

  obtain supr' psupr' where Supr' : "supr = mdp psupr' supr'" "supr' \<in> S s"
    using V_valid Hsup_in
    by(auto simp add: prio_l_S_def split: md_prio.splits)

  obtain supr_res' psupr_res' where Result : "LMap (prio_l f0 f1 l) f s supr = mdp psupr_res' supr_res'"
    by(cases "LMap (prio_l f0 f1 l) f s supr"; auto)

  show "is_sup (LMap (prio_l f0 f1 l) f s ` V) (LMap (prio_l f0 f1 l) f s supr)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (prio_l f0 f1 l) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (prio_l f0 f1 l) f s xo = x"
      by auto

    have "xo <[ supr" using is_supD1[OF Hsup Xo(1)] by simp

    have "x \<in> prio_l_S S s" 
      using put_S Xo
      by(cases l; auto simp add: prio_l_S_def prio_l_def split: md_prio.splits)

    then obtain x' px' where X' : "x = mdp px' x'" "x' \<in> S s"
      by(auto simp add: prio_l_S_def split: md_prio.splits)

    obtain xo' pxo' where Xo' : "xo = mdp pxo' xo'" "xo' \<in> S s" using Xo Vsubs
      by(cases xo; auto simp add: prio_l_S_def split: md_prio.splits)

    show "x <[ LMap (prio_l f0 f1 l) f s supr"
    proof(cases "pxo' = psupr'")
      case True

      then have "xo' <[ supr'" using Xo' Supr' `xo <[ supr`
        by(simp add: prio_pleq)

      hence "is_sup {xo', supr'} supr'"
        using is_sup_pair by auto
  
      hence Conc' : "is_sup (LMap l f s ` {xo', supr'}) (LMap l f s supr')"
        using Xo' Supr' pres[of xo' "{xo', supr'}" s supr' f] 
        by auto

      then show ?thesis
        using is_supD1[OF Conc', of x'] X' Xo Xo' Supr'
        using f1_mono_leq[of pxo' psupr'] True
        by(auto simp add: prio_l_def prio_pleq split: md_prio.splits)
    next
      case False

      then have "pxo' < psupr'"
        using `xo <[ supr` Xo' Supr'
        by(auto simp add: prio_pleq split: if_split_asm)

      have "px' < psupr_res'" using f1_mono_lt[OF `pxo' < psupr'`, of s]
          Result X' Xo Xo' Supr'
        by(auto simp add: prio_l_def)

      then show ?thesis using X' Xo Xo' Supr' X' Result
        by(auto simp add:prio_pleq split: md_prio.splits)
    qed
  next

    fix zo

    assume Ub : "is_ub (LMap (prio_l f0 f1 l) f s ` V) zo" 

    obtain zo' pzo' where Z' : "zo = mdp pzo' zo'"
      by(cases zo; auto)

    have Psupr_res'_eq :
      "psupr_res' = f1 s psupr'"
      using Supr' Result
      by(cases l; auto simp add: prio_l_def prio_pleq split: md_prio.splits if_splits)

    obtain Vmax where VSmax : "Vmax = {w . w \<in> V \<and> 
      (\<exists> w' pw' . w = mdp pw' w' \<and>
       (\<forall> y y' py' . y \<in> V \<longrightarrow> y = mdp py' y' \<longrightarrow> py' \<le> pw'))}"
      by auto

    have VSmax_eq : "\<And> w y pw' w' py' y' .
      w \<in> Vmax \<Longrightarrow> y \<in> Vmax \<Longrightarrow>
      w = mdp pw' w' \<Longrightarrow>
      y = mdp py' y' \<Longrightarrow>
      pw' = py'"
    proof-
      fix w y pw' w' py' y'
      assume Hw1 : "w \<in> Vmax"
      assume Hy1 : "y \<in> Vmax"
      assume Hwp1 : "w = mdp pw' w'"
      assume Hyp1 : "y = mdp py' y'"

      have Hw1_v : "w \<in> V" using VSmax Hw1 by blast
      have Hy1_v : "y \<in> V" using VSmax Hy1 by blast


      have "py' \<le> pw'"
        using Set.subsetD[OF Set.equalityD1[OF VSmax] Hw1] Hy1_v Hyp1 Hwp1
        by auto

      have "pw' \<le> py'"
        using Set.subsetD[OF Set.equalityD1[OF VSmax] Hy1] Hw1_v Hyp1 Hwp1
        by auto

      show "pw' = py'"
        using `py' \<le> pw'` `pw' \<le> py'`
        by auto
    qed

    have Vmax_fact2 : "\<And> n . Vmax = {} \<Longrightarrow>
      (\<exists> w pw' w' . w \<in> V \<and> w = mdp pw' w' \<and> pw' > n)"
    proof-
      fix n
      assume Contr : "Vmax = {}"
      then show "(\<exists> w pw' w' . w \<in> V \<and> w = mdp pw' w' \<and> pw' > n)"
      proof(induction n)
        case 0
        then show ?case unfolding VSmax using V' Nemp apply(auto)
          apply(drule_tac x = v in spec)
          apply(auto)
          done
      next
        case (Suc n)

        obtain w pw' w' where W: "w \<in> V" "w = mdp pw' w'" "n < pw'"
          using Suc.IH[OF Suc.prems] by auto

        show ?case using W Suc.prems
          unfolding VSmax using V' Nemp apply(auto)
          apply(drule_tac x = w in spec)
          apply(auto)
          done
      qed
    qed

    have Psupr'_max : "\<And> w pw' w' . w \<in> V \<Longrightarrow> w = mdp pw' w' \<Longrightarrow> pw' \<le> psupr'"
    proof-
      fix w pw' w'
      assume H1 :"w \<in> V"
      assume H2 : "w = mdp pw' w'"

      show "pw' \<le> psupr'"
        using is_supD1[OF Hsup H1] H2 Supr'
        by(auto simp add: prio_pleq split:if_splits)
    qed

    have VSmax_nemp : "Vmax = {} \<Longrightarrow> False"
    proof-

      assume Contr : "Vmax = {}"

      obtain w pw' w' where W: "w \<in> V" "w = mdp pw' w'" "psupr' < pw'"
        using Vmax_fact2[OF Contr, of psupr']
        by auto

      show False using Psupr'_max[OF W(1) W(2)] W(3)
        by(auto)
    qed

    hence "Vmax \<noteq> {}" by auto

    then obtain m where M : "m \<in> Vmax"
      unfolding sym[OF ex_in_conv]
      by(auto)

    obtain pm' m' where M' : "m = mdp pm' m'"
      by(cases m; auto)

    have "m \<in> V"
      using VSmax M by auto

    obtain Vmaxp where VSmaxp : "Vmaxp = (\<lambda> x . (case x of (mdp px' x') \<Rightarrow> px')) ` Vmax"
      by simp

    obtain Vmaxv where VSmaxv : "Vmaxv = (\<lambda> x . (case x of (mdp px' x') \<Rightarrow> x')) ` Vmax"
      by simp

    have In_Vmax  :
      "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
        y \<in> V \<Longrightarrow> y = mdp py' y'\<Longrightarrow> py'\<le> pw'"
      unfolding VSmax
      by blast

    have In_Vmax_Conv :       
      "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
        y \<in> V \<Longrightarrow> y = mdp pw' y'\<Longrightarrow> y \<in> Vmax"
      unfolding VSmax
      by(auto)

    have Notin_Vmax : 
      "\<And> w pw' w' y y' py'. w \<in> Vmax \<Longrightarrow>  w = mdp pw' w' \<Longrightarrow>
        y \<in> V \<Longrightarrow> y \<notin> Vmax \<Longrightarrow> y = mdp py' y'\<Longrightarrow> py' < pw'"
    proof-
      fix w pw' w' y y' py'
      assume Win : "w \<in> Vmax"
      assume W' : "w = mdp pw' w'"
      assume Yin : "y \<in> V"
      assume Ynotin : "y \<notin> Vmax"
      assume Y' : "y = mdp py' y'"

      have "py' \<le> pw'" using In_Vmax[OF Win W' Yin Y'] by simp

      show "py' < pw'"
      proof(cases "py' = pw'")
        case False
        then show ?thesis using `py' \<le> pw'` by simp
      next
        case True

        then have "y \<in> Vmax" using In_Vmax_Conv[OF Win W' Yin] Y'
          by auto

        then have False using Ynotin by simp

        thus ?thesis by simp
      qed
    qed

    (* do we need this? *)
    have "is_sup Vmax supr"
    proof(rule is_supI)
      fix x
      assume "x \<in> Vmax"
      then have Hx : "x \<in> V" unfolding VSmax by auto


      show "x <[ supr" using is_supD1[OF Hsup Hx] by simp
    next
      fix w
      assume Ub : "is_ub Vmax w"

      have Ub' : "is_ub V w"
      proof(rule is_ubI)
        fix x
        assume X : "x \<in> V"

        obtain x' px' where X' : "x = mdp px' x'" by(cases x; auto)

        have "px' \<le> pm'"
          using In_Vmax[OF M M' X X'] by simp

        obtain w' pw' where W' : "w = mdp pw' w'" by(cases w; auto)

        have "m <[ w" using is_ubE[OF Ub M] by simp

        then show "x <[ w"
        proof(cases "x \<in> Vmax")
          case True
          then show ?thesis using is_ubE[OF Ub, of x] by simp
        next
          case False

          then have "px' < pm'"
            using Notin_Vmax[OF M M' X False X'] by simp

          then show ?thesis using X' W' M' `m <[ w`
            by(auto simp add: prio_pleq split: if_splits)
        qed
      qed
      show "supr <[ w"
        using is_supD2[OF Hsup Ub'] by simp
    qed

    (* idea: either pm' is equal to supr, or is one less. *)
    show "LMap (prio_l f0 f1 l) f s supr <[ zo"
    proof(cases "has_sup Vmaxv")
      case False

      consider (L) "psupr' < 1 + pm'"
        | (E) "psupr' = 1 + pm'"
        | (G) "psupr' > 1 + pm'"
        using less_linear by auto

      then have Psupr_Inc : "psupr' = 1 + pm'"
      proof cases
        case L

        then have Eq : "psupr' = pm'" using Psupr'_max[OF `m \<in> V` M'] by simp

        have "is_sup Vmaxv supr'"
        proof(rule is_supI)
          fix w'
          assume W': "w' \<in> Vmaxv"

          obtain pw' where W: "(mdp pw' w') \<in> Vmax" using W'
            unfolding VSmaxv
            by(auto split: md_prio.splits)

          have Pw' : "pw' = pm'"
            using VSmax_eq[OF M W M']
            by auto

          have "mdp pw' w' <[ supr" using is_supD1[OF `is_sup Vmax supr` W]
            by simp

          then show "w' <[ supr'"
            using Eq Pw' Supr'
            by(auto simp add: prio_pleq)
        next
          fix z'

          assume Z' : "is_ub Vmaxv z'"

          have Zmax : "is_ub Vmax (mdp pm' z')"
          proof(rule is_ubI)
            fix w
            assume W : "w \<in> Vmax"

            obtain pw' w' where W' : "w = mdp pw' w'" by(cases w; auto)

            have Pw' : "pw' = pm'"
              using VSmax_eq[OF M W M' W'] by simp

            have "w' \<in> Vmaxv" using W W'
              unfolding VSmaxv using imageI[OF W, of "case_md_prio (\<lambda>px' x'. x')"]
              by auto

            then have "w' <[ z'"
              using is_ubE[OF Z'] by auto

            then show "w <[ mdp pm' z'" using Pw' W'
              by(auto simp add: prio_pleq split:if_splits)
          qed
          
          show "supr' <[ z'" using is_supD2[OF `is_sup Vmax supr` Zmax] Eq Supr'
            by(auto simp add: prio_pleq split:if_splits)
        qed

        then have False using False by(auto simp add: has_sup_def)

        then show "psupr' = 1 + pm'" by simp
      next
        case E
        then show ?thesis by simp
      next
        case G

        have Supr_Ub : "is_ub V (mdp (1 + pm') supr')"
        proof(rule is_ubI)
          fix w

          assume W : "w \<in> V"

          obtain pw' w' where W' : "w = mdp pw' w'" by(cases w; auto)

          have "pw' \<le> pm'" using In_Vmax[OF M M' W W'] by simp

          then show "w <[ mdp (1 + pm') supr'"
            using W'
            by(auto simp add: prio_pleq)
        qed

        then have "mdp psupr' supr' <[ mdp (1 + pm') supr'"
          using is_supD2[OF `is_sup V supr` Supr_Ub] Supr'
          by auto

        then have False using G
          by(auto simp add: prio_pleq split:if_splits)

        then show ?thesis by simp
      qed

      have "is_ub Vmax (mdp (1 + pm') \<bottom>)"
      proof(rule is_ubI)
        fix w

        assume W: "w \<in> Vmax"

        obtain pw' w' where W' : "w = mdp pw' w'" by(cases w; auto)

        have "pw' = pm'" using VSmax_eq[OF W M W' M'] by simp

        then show "w <[ mdp (1 + pm') \<bottom>"
          using W'
          by(auto simp add: prio_pleq)
      qed

      hence "supr <[ (mdp (1 + pm') \<bottom>)"
        using is_supD2[OF `is_sup Vmax supr`] by auto

      hence "supr = (mdp (1 + pm') \<bottom>)"
        using Supr' Psupr_Inc leq_antisym[OF bot_spec[of supr']]
        by(auto simp add: prio_pleq bot_spec)

      hence False using bot_bad Supr'
        by auto

      thus ?thesis by auto
    next
      case True

      then obtain vsup where Vsup : "is_sup Vmaxv vsup"
        by(auto simp add: has_sup_def)

      have "is_ub V (mdp pm' vsup)"
      proof(rule is_ubI)
        fix z
        assume Z: "z \<in> V"
        obtain pz' z' where Z' : "z = mdp pz' z'"
          by(cases z; auto)

        show "z <[ mdp pm' vsup"
        proof(cases "z \<in> Vmax")
          case True

          have "z' \<in> Vmaxv"
            using imageI[OF True, of "case_md_prio (\<lambda>px' x'. x')"] Z'
            unfolding VSmaxv
            by auto

          have "pz' = pm'"
            using VSmax_eq[OF True M Z' M'] by simp

          have "z' <[ vsup"
            using is_supD1[OF Vsup `z' \<in> Vmaxv`] by simp

          then show ?thesis using `pz' = pm'` Z'
            by(auto simp add: prio_pleq)
        next
          case False
          have "pz' < pm'"
            using Notin_Vmax[OF M M' Z False Z'] by simp

          then show ?thesis using Z'
            by(auto simp add: prio_pleq)
        qed
      qed

      have Supr_Vmax : "is_sup Vmaxv supr'"
      proof(rule is_supI)
        fix w'

        assume W': "w' \<in> Vmaxv"

        obtain pw' where W: "(mdp pw' w') \<in> Vmax" using W'
          unfolding VSmaxv
          by(auto split: md_prio.splits)

        have Pw' : "pw' = pm'"
          using VSmax_eq[OF M W M']
          by auto

        have "mdp pw' w' <[ supr" using is_supD1[OF `is_sup Vmax supr` W]
          by simp


        have "pw' = psupr'"
          using is_supD2[OF Hsup `is_ub V (mdp pm' vsup)`]
            Pw' Supr' `mdp pw' w' <[ supr`
          by(auto simp add: prio_pleq split: if_splits)

        then show "w' <[ supr'"
          using Pw' Supr' `mdp pw' w' <[ supr`
          by(auto simp add: prio_pleq)
      next

        fix w'

        assume W' : "is_ub Vmaxv w'"

        have "is_ub V (mdp pm' w')"
        proof(rule is_ubI)
          fix z
          assume Z: "z \<in> V"
          obtain pz' z' where Z' : "z = mdp pz' z'"
            by(cases z; auto)

          show "z <[ mdp pm' w'"
          proof(cases "z \<in> Vmax")
            case True

            then have "z' \<in> Vmaxv" 
              using imageI[OF True, of "case_md_prio (\<lambda>px' x'. x')"] Z'
              unfolding VSmaxv
              by auto
              
            have "z' <[ w'" using is_ubE[OF W' `z' \<in> Vmaxv`] by simp

            have "pz' = pm'" using VSmax_eq[OF True M Z' M'] by simp

            then show ?thesis using `z' <[ w'` Z'
              by(auto simp add: prio_pleq split: md_prio.splits)
          next
            case False

            have "pz' < pm'"
              using Notin_Vmax[OF M M' Z False Z'] by simp

            then show ?thesis using Z'
              by(auto simp add: prio_pleq)
          qed
        qed

        have "m' \<in> Vmaxv" using M' M
          unfolding VSmaxv
          using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
          by(auto)

        have "m' <[ w'"
          using is_ubE[OF W' `m' \<in> Vmaxv`] by simp

        have "supr <[ (mdp pm' w')"
          using is_supD2[OF Hsup `is_ub V (mdp pm' w')`]
          by simp

        have "m \<in> V" using M unfolding VSmax by auto

        have "pm' \<le> psupr'"
          using Psupr'_max[OF `m \<in> V` M'] by simp

        hence "pm' = psupr'"
          using `supr <[ (mdp pm' w')` Supr'
          by(auto simp add: prio_pleq split: if_splits)

        then show "supr' <[ w'"
          using Supr' `supr <[ mdp pm' w'`
          by(auto simp add: prio_pleq split: if_splits)
      qed

      have "m' \<in> Vmaxv" using M' M
        unfolding VSmaxv
        using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
        by(auto)

      have "Vmaxv \<subseteq> S s"
        using Vsubs
        unfolding VSmax VSmaxv
        by auto

      have Supr'_sup_vmax : "is_sup (LMap l f s ` Vmaxv) (LMap l f s supr')"
        using pres[OF `m' \<in> Vmaxv` `Vmaxv \<subseteq> S s` 
            `is_sup Vmaxv supr'` Supr'(2)]
        by simp

      consider (L) "pm' < psupr'"
        | (E) "pm' = psupr'"
        | (G) "pm' > psupr'"
        using less_linear by auto
      then have "pm' = psupr'"
      proof cases
        case L

        have "is_ub V (mdp pm' supr')"
        proof(rule is_ubI)
          fix w
          assume W : "w \<in> V"

          obtain pw' w' where W' : "w = mdp pw' w'"
            by(cases w; auto)

          show "w <[ mdp pm' supr'"
          proof(cases "w \<in> Vmax")
            case True

            have "pw' = pm'" using VSmax_eq[OF True M W' M'] by simp

            have "w' \<in> Vmaxv"
              using imageI[OF True, of "case_md_prio (\<lambda>px' x'. x')"] W'
              unfolding VSmaxv by auto

            then have "w' <[ supr'"
              using is_supD1[OF `is_sup Vmaxv supr'`] by auto

            then show "w <[ mdp pm' supr'"
              using `pw' = pm'` W'
              by(auto simp add: prio_pleq split: if_splits)
          next
            case False

            have "pw' < pm'" using Notin_Vmax[OF M M' W False W'] by simp

            then show "w <[ mdp pm' supr'"
              using W'
              by(auto simp add: prio_pleq split: if_splits)
          qed
        qed

        have "mdp psupr' supr' <[ mdp pm' supr'"
          using is_supD2[OF Hsup `is_ub V (mdp pm' supr')`] Supr'
          by auto

        then have False using L
          by(auto simp add: prio_pleq split: if_splits)

        then show ?thesis by simp
      next
        case E
        then show ?thesis by simp
      next
        case G

        have "m \<in> V" using M
          unfolding VSmax by auto

        have "mdp pm' m' <[ mdp psupr' supr'"
          using is_supD1[OF Hsup `m \<in> V`] M' Supr'
          by auto

        hence False using G
          by(auto simp add: prio_pleq split: if_splits)

        then show ?thesis by simp
      qed

      consider (L) "pzo' < f1 s pm'"
        | (E) "pzo' = f1 s pm'"
        | (G) "pzo' > f1 s pm'"
        using less_linear by auto
      then show "LMap (prio_l f0 f1 l) f s supr <[ zo"
      proof cases
        case L

        have "m \<in> V"
          using M VSmax by auto
        
        have Bad : "LMap (prio_l f0 f1 l) f s m \<in> LMap (prio_l f0 f1 l) f s ` V"
          using imageI[OF `m \<in> V`, of "LMap (prio_l f0 f1 l) f s"]
          by auto

        have False using is_ubE[OF Ub Bad] L M' Z'
          by(cases l; auto simp add: prio_l_def prio_pleq)

        then show ?thesis by simp
      next
        case E

        have Ub_max : "is_ub (LMap l f s ` Vmaxv) zo'"
        proof(rule is_ubI)
          fix wo'
          assume Wo' : "wo' \<in>  LMap l f s ` Vmaxv "

          obtain w pw' w' where W: "w = mdp pw' w'" "w \<in> Vmax" "LMap l f s w' = wo'" using Wo'
            unfolding VSmaxv
            by(auto split: md_prio.splits)

          have "pw' = pm'"
            using VSmax_eq[OF M `w \<in> Vmax` M' `w = mdp pw' w'`]
            by simp

          have "w \<in> V" using `w \<in> Vmax`
            unfolding VSmax by auto

          have Wmap : "LMap (prio_l f0 f1 l) f s w \<in> (LMap (prio_l f0 f1 l) f s ` V)"
            using imageI[OF `w \<in> V`] by auto

          have "LMap (prio_l f0 f1 l) f s w <[ zo"
            using is_ubE[OF Ub Wmap]  by simp

          then show "wo' <[ zo'"
            using Z' `pw' = pm'` E W
            by(cases l; auto simp add: prio_l_def prio_pleq)
        qed

        then show ?thesis using is_supD2[OF Supr'_sup_vmax Ub_max] E `pm' = psupr'` Z' Supr' Result
          by(cases l; auto simp add: prio_l_def prio_pleq)
      next
        case G
        have "m' \<in> Vmaxv" using M' M
          unfolding VSmaxv
          using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
          by(auto)

        have "m \<in> V" using M unfolding VSmax by auto

        have "m' \<in> Vmaxv" using M' M
          unfolding VSmaxv
          using imageI[OF M, of "case_md_prio (\<lambda>px' x'. x')"]
          by(auto)

        then show ?thesis using Supr' Z' G `pm' = psupr'`
          by(cases l; auto simp add: prio_l_def prio_pleq)
      qed
    qed
  qed
next
  show "\<And>s. \<bottom> \<notin> prio_l_S S s" using bot_bad
    by(auto simp add: prio_bot prio_l_S_def)
qed

lemma (in prio_l_valid_base_ok_pres) ax :
  shows "lifting_valid_base_ok_pres (prio_l f0 f1 l) (prio_l_S S)"
  using out.lifting_valid_base_ok_pres_axioms
  by auto

(* TODO: corresponding "stronger" version of this property may be helpful,
 *)
lemma (in prio_l_valid_base_ok_pres) ax_g :
  assumes H : "\<And> x . S' x = prio_l_S S x"
  shows "lifting_valid_base_ok_pres (prio_l f0 f1 l) S'"
proof-
  have "S' = prio_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_base_ok_pres_axioms assms
  by auto
qed

locale prio_l_pairwise' = 
  fixes S :: "('syn, 'b :: {Pordbc, Pordps}) valid_set"

locale prio_l_valid_pairwise_ext = prio_l_pairwise' +
  lifting_valid_pairwise_ext

lemma prio_sup_cases :
  assumes H: "is_sup {x1 :: ('a :: Pordbc) md_prio, x2} supr"
  shows "supr = x1 \<or> supr = x2 \<or>
    (\<exists> px1' x1' px2' x2' psupr' supr' . x1 = mdp px1' x1' \<and> x2 = mdp px2' x2' \<and> supr = mdp psupr' supr' \<and> 
    ((px1' = px2' \<and> px1' = psupr' \<and> is_sup {x1', x2'} (supr')) \<or>
    (px1' = px2' \<and> psupr' = 1 + px1' \<and> supr' = \<bottom>)))"
proof-

  obtain px1' x1' where X1 : "x1 = mdp px1' x1'"
    by(cases x1; auto)

  obtain px2' x2' where X2 : "x2 = mdp px2' x2'"
    by(cases x2; auto)

  obtain psupr' supr' where Supr : "supr = mdp psupr' supr'"
    by(cases supr; auto)

  consider (X2_Max) "px1' < px2'" |
           (X1_Max) "px2' < px1'" |
           (Eq) "px1' = px2'"
    by arith
  then show ?thesis
  proof cases
    case X2_Max

    then have "x1 <[ x2"
      using X1 X2 by(auto simp add: prio_pleq)

    then have "is_sup {x1, x2} x2"
      using is_sup_pair by auto

    then have "supr = x2"
      using is_sup_unique[OF H]
      by auto

    then show ?thesis by auto
  next
    case X1_Max

    have Comm : "{x2, x1} = {x1, x2}"
      by auto

    have "x2 <[ x1"
      using X1 X2 X1_Max by(auto simp add: prio_pleq)

    then have "is_sup {x2, x1} x1"
      using is_sup_pair by auto

    then have "is_sup {x1, x2} x1" using Comm
      by auto

    then have "supr = x1"
      using is_sup_unique[OF H]
      by auto

    then show ?thesis by auto
  next
    case Eq
    show ?thesis
    proof(cases "has_sup {x1', x2'}")
      case True

      then obtain supr'_alt where Supr'_alt : "is_sup {x1', x2'} supr'_alt"
        by(auto simp add: has_sup_def)

      have Supr'_alt' : "is_sup {x1, x2} (mdp px1' supr'_alt)"
      proof(rule is_supI)
        fix x
        assume "x \<in> {x1, x2}"

        then consider (1) "x = x1" | (2) "x = x2"
          by auto
        then show "x <[ mdp px1' supr'_alt"
        proof cases
          case 1
          then show ?thesis using is_supD1[OF Supr'_alt] X1 X2 Eq
            by(auto simp add: prio_pleq)
        next
          case 2
          then show ?thesis using is_supD1[OF Supr'_alt] X1 X2 Eq
            by(auto simp add: prio_pleq)
        qed
      next
        fix w

        assume Ub : "is_ub {x1, x2} w"

        obtain pw' w' where W : "w = mdp pw' w'"
          by(cases w; auto)

        consider (1) "pw' < px1'" | (2) "pw' = px1'" | (3) "px1' < pw'"
          by arith
        then show "mdp px1' supr'_alt <[ w"
        proof cases
          case 1

          then have False using is_ubE[OF Ub, of x1] X1 W
            by(auto simp add: prio_pleq)

          then show ?thesis by auto
        next
          case 2

          have X1'_leq : "x1' <[ w'"
            using 2 is_ubE[OF Ub, of x1] X1 W
            by(auto simp add: prio_pleq)

          have X2'_leq : "x2' <[ w'"
            using 2 is_ubE[OF Ub, of x2] X2 W Eq
            by(auto simp add: prio_pleq)

          have Ub' : "is_ub {x1', x2'} w'"
            using X1 X2 W X1'_leq X2'_leq Eq 2
            by(auto simp add: is_ub_def prio_pleq)

          then have "supr'_alt <[ w'"
            using is_supD2[OF Supr'_alt]
            by auto

          then show ?thesis using 2 Eq W
            by(auto simp add: prio_pleq)
        next
          case 3
          then show ?thesis
            using W
            by(auto simp add: prio_pleq)
        qed
      qed

      then have "supr = mdp px1' supr'_alt"
        using is_sup_unique[OF Supr'_alt' H]
        by auto

      then have "px1' = px2' \<and>
          px1' = psupr' \<and> is_sup {x1', x2'} (supr') "
        using Eq Supr Supr'_alt
        by(auto)

      then show ?thesis using X1 X2 Supr by auto
    next
      case False

      have Supr_alt : "is_sup {x1, x2} (mdp (1 + px1') \<bottom>)"
      proof(rule is_supI)
        fix x

        assume "x \<in> {x1, x2}"

        then show "x <[ mdp (1 + px1') \<bottom>"
          using X1 X2 Eq
          by(auto simp add: prio_pleq)
      next
        fix w

        assume Ub : "is_ub {x1, x2} w"

        obtain pw' w' where W : "w = mdp pw' w'"
          by(cases w; auto)

        have "x1 <[ w"
          using is_ubE[OF Ub, of x1]
          by auto

        then have "px1' \<le> pw'"
          using X1 W
          by(auto simp add: prio_pleq split:if_splits)

        then consider (1) "pw' = px1'" | (2) "1 + px1' = pw'" | (3) "1 + px1' < pw'"
          by arith

        then show "mdp (1 + px1') \<bottom> <[ w"
        proof cases
          case 1

          then have "is_ub {x1', x2'} w'"
            using X1 X2 W Ub Eq
            by(auto simp add: is_ub_def prio_pleq split: if_splits)

          then have "has_sup {x1', x2'}"
            using complete2
            by(auto simp add: has_ub_def)

          then have False using False by auto

          then show ?thesis by auto
        next
          case 2
          then show ?thesis
            using W bot_spec
            by(auto simp add: prio_pleq)
        next
          case 3
          then show ?thesis using W
            by(auto simp add: prio_pleq)
        qed
      qed

      have Supr_alt' : "supr = (mdp (1 + px1') \<bottom>)"
        using is_sup_unique[OF H Supr_alt]
        by auto

      then have "px1' = px2' \<and> psupr' = 1 + px1' \<and> supr' = \<bottom>"
        using Eq Supr
        by(auto)

      then show ?thesis using X1 X2 Supr Eq by auto
    qed
  qed
qed

lemma prio_sup_overflow :
  assumes H : "\<not> has_sup {(x' :: ('a :: Pordbc)), y'}"
  assumes HP : "px' = py'"
  shows "is_sup {mdp px' x', mdp py' y'} (mdp (1 + px') \<bottom>)"
proof(rule is_supI)
  fix x
  assume "x \<in> {mdp px' x', mdp py' y'}" 
  then show "x <[ mdp (1 + px') \<bottom>"
    using HP
    by(auto simp add: prio_pleq)
next
  fix w
  assume Ub : "is_ub {mdp px' x', mdp py' y'} w"

  obtain pw' w' where W : "w = mdp pw' w'"
    by(cases w; auto)

  have "mdp px' x' <[ w"
    using is_ubE[OF Ub]
    by auto

  then have "px' \<le> pw'"
    using W
    by(auto simp add: prio_pleq split:if_splits)

  then consider (1) "pw' = px'" | (2) "1 + px' = pw'" | (3) "1 + px' < pw'"
    by arith

  then show "mdp (1 + px') \<bottom> <[ w"
  proof cases
    case 1

    then have "is_ub {x', y'} w'"
      using W Ub HP
      by(auto simp add: is_ub_def prio_pleq split: if_splits)

    then have "has_sup {x', y'}"
      using complete2[of x' y']
      by(auto simp add: has_ub_def)

    then have False using H by auto

    then show ?thesis by auto
  next
    case 2
    then show ?thesis
      using W bot_spec
      by(auto simp add: prio_pleq)
  next
    case 3
    then show ?thesis using W
      by(auto simp add: prio_pleq)
  qed
qed

lemma prio_sup_inner:
  assumes H : "is_sup {(x' :: ('a :: Pordbc)), y'} supr"
  assumes HP : "px' = py'"
  shows "is_sup {mdp px' x', mdp py' y'} (mdp px' supr)"
proof(rule is_supI)
  fix x
  assume "x \<in> {mdp px' x', mdp py' y'}" 
  then show "x <[ (mdp px' supr)"
    using HP is_supD1[OF H, of "x'"] is_supD1[OF H, of "y'"]
    by(auto simp add: prio_pleq)
next
  fix w
  assume Ub : "is_ub {mdp px' x', mdp py' y'} w"

  obtain pw' w' where W : "w = mdp pw' w'"
    by(cases w; auto)

  have "mdp px' x' <[ w"
    using is_ubE[OF Ub]
    by auto

  then have "px' \<le> pw'"
    using W
    by(auto simp add: prio_pleq split:if_splits)

  then consider (1) "pw' = px'" | (2) "1 + px' = pw'" | (3) "1 + px' < pw'"
    by arith

  then show "mdp px' supr <[ w"
  proof cases
    case 1

    then have "is_ub {x', y'} w'"
      using W Ub HP
      by(auto simp add: is_ub_def prio_pleq split: if_splits)

    then show ?thesis using is_supD2[OF H] W 1
      by(auto simp add: prio_pleq)
  next
    case 2
    then show ?thesis
      using W bot_spec
      by(auto simp add: prio_pleq)
  next
    case 3
    then show ?thesis using W
      by(auto simp add: prio_pleq)
  qed
qed


sublocale prio_l_valid_pairwise_ext \<subseteq> out : lifting_valid_pairwise_ext "prio_l_S S"
proof

  fix s
  fix x1 x2 x3 s12 s13 s23 s123 :: "'b md_prio"
  assume X1 : "x1 \<in> prio_l_S S s"
  assume X2 :"x2 \<in> prio_l_S S s"
  assume X3 : "x3 \<in> prio_l_S S s"
  assume S12 :"is_sup {x1, x2} s12"
  assume S12_in :"s12 \<in> prio_l_S S s"
  assume S23 :"is_sup {x2, x3} s23"
  assume S23_in :"s23 \<in> prio_l_S S s"
  assume S13 :"is_sup {x1, x3} s13" 
  assume S13_in :"s13 \<in> prio_l_S S s"  
  assume S123 :"is_sup {x1, x2, x3} s123"

  obtain px1' x1' where X1' : "x1 = mdp px1' x1'"
    by(cases x1; auto)

  obtain px2' x2' where X2' : "x2 = mdp px2' x2'"
    by(cases x2; auto)

  obtain px3' x3' where X3' : "x3 = mdp px3' x3'"
    by(cases x3; auto)

  obtain py1' y1' py2' y2' py3' y3' where Ys :
    "{mdp px1' x1', mdp px2' x2', mdp px3' x3'} = {mdp py1' y1', mdp py2' y2', mdp py3' y3'}"
    "py1' \<le> py2'" "py2' \<le> py3'"
    by (metis (full_types) insert_commute linear) 

  have Y1_in : "mdp py1' y1' \<in> prio_l_S S s"
    using Ys(1) S12 X1 X2 X3
    unfolding X1' X2' X3' by auto

  have Y2_in : "mdp py2' y2' \<in> prio_l_S S s"
    using Ys(1) S12 X1 X2 X3
    unfolding X1' X2' X3' by auto

  have Y3_in : "mdp py3' y3' \<in> prio_l_S S s"
    using Ys(1) S12 X1 X2 X3
    unfolding X1' X2' X3' by auto

(* TODO: these are slower than they should be. *)
  have Y1_cases : "mdp py1' y1' = mdp px1' x1' \<or> mdp py1' y1' = mdp px2' x2' \<or> mdp py1' y1' = mdp px3' x3'"
    using Ys(1)
    by(fastforce)

  have Y2_cases : "mdp py2' y2' = mdp px1' x1' \<or> mdp py2' y2' = mdp px2' x2' \<or> mdp py2' y2' = mdp px3' x3'"
    using Ys(1)
    by(fastforce)

  have Y3_cases : "mdp py3' y3' = mdp px1' x1' \<or> mdp py3' y3' = mdp px2' x2' \<or> mdp py3' y3' = mdp px3' x3'"
    using Ys(1)
    by(fastforce)

(* degenerate cases *)
  have X1_dgn : "is_sup {x1, x1} x1"
    using sup_singleton[of x1]
    by fastforce

  have X2_dgn : "is_sup {x2, x2} x2"
    using sup_singleton[of x2]
    by fastforce 

  have X3_dgn : "is_sup {x3, x3} x3"
    using sup_singleton[of x3]
    by fastforce

  consider (Y1to1) "mdp py1' y1' = mdp px1' x1'" | (Y1to2) "mdp py1' y1' = mdp px2' x2'" | (Y1to3) "mdp py1' y1' = mdp px3' x3'"
    using Y1_cases by auto
  then have "\<exists> sy12 . is_sup {mdp py1' y1', mdp py2' y2'} sy12 \<and> sy12 \<in> prio_l_S S s"
  proof cases
    case Y1to1
    consider (Y2to1) "mdp py2' y2' = mdp px1' x1'" | (Y2to2) "mdp py2' y2' = mdp px2' x2'" | (Y2to3) "mdp py2' y2' = mdp px3' x3'"
      using Y2_cases by auto
    then show ?thesis
    proof cases
      case Y2to1
      then show ?thesis 
        using Y1to1 X1_dgn X1
        unfolding X1'
        by auto
    next
      case Y2to2
      then show ?thesis 
        using Y1to1 S12 S12_in
        unfolding X1' X2'
        by(auto)
    next
      case Y2to3
      then show ?thesis
        using Y1to1 S13 S13_in
        unfolding X1' X3'
        by(auto)
    qed
  next
    case Y1to2
    consider (Y2to1) "mdp py2' y2' = mdp px1' x1'" | (Y2to2) "mdp py2' y2' = mdp px2' x2'" | (Y2to3) "mdp py2' y2' = mdp px3' x3'"
      using Y2_cases by auto
    then show ?thesis
    proof cases
      case Y2to1
      have Comm : "{mdp py1' y1', mdp py2' y2'} = {mdp py2' y2', mdp py1' y1'}"
        by auto
      show ?thesis using Y2to1
        using Y1to2 S12 S12_in
        unfolding X1' X2' Comm
        by(auto)
    next
      case Y2to2
      then show ?thesis 
        using Y1to2 X2_dgn X2
        unfolding X2'
        by auto
    next
      case Y2to3
      then show ?thesis
        using Y1to2 S23 S23_in
        unfolding X2' X3'
        by(auto)
    qed
  next
    case Y1to3
    consider (Y2to1) "mdp py2' y2' = mdp px1' x1'" | (Y2to2) "mdp py2' y2' = mdp px2' x2'" | (Y2to3) "mdp py2' y2' = mdp px3' x3'"
      using Y2_cases by auto
    then show ?thesis
    proof cases
      case Y2to1
      have Comm : "{mdp py1' y1', mdp py2' y2'} = {mdp py2' y2', mdp py1' y1'}"
        by auto
      show ?thesis using Y2to1
        using Y1to3 S13 S13_in
        unfolding X1' X3' Comm
        by(auto)
    next
      case Y2to2
      have Comm : "{mdp py1' y1', mdp py2' y2'} = {mdp py2' y2', mdp py1' y1'}"
        by auto
      show ?thesis 
        using Y2to2 Y1to3 S23 S23_in
        unfolding X2' X3' Comm
        by(auto)
    next
      case Y2to3
      then show ?thesis
        using Y1to3 X3_dgn X3
        unfolding X2' X3'
        by(auto)
    qed
  qed

  then obtain sy12 where Sy12 : "is_sup {mdp py1' y1', mdp py2' y2'} sy12" "sy12 \<in> prio_l_S S s"
    by auto

  consider (Y2to1) "mdp py2' y2' = mdp px1' x1'" | (Y2to2) "mdp py2' y2' = mdp px2' x2'" | (Y2to3) "mdp py2' y2' = mdp px3' x3'"
    using Y2_cases by auto
  then have "\<exists> sy23 . is_sup {mdp py2' y2', mdp py3' y3'} sy23 \<and> sy23 \<in> prio_l_S S s"
  proof cases
    case Y2to1
    consider (Y3to1) "mdp py3' y3' = mdp px1' x1'" | (Y3to2) "mdp py3' y3' = mdp px2' x2'" | (Y3to3) "mdp py3' y3' = mdp px3' x3'"
      using Y3_cases by auto
    then show ?thesis
    proof cases
      case Y3to1
      then show ?thesis 
        using Y2to1 X1_dgn X1
        unfolding X1'
        by auto
    next
      case Y3to2
      then show ?thesis 
        using Y2to1 S12 S12_in
        unfolding X1' X2'
        by(auto)
    next
      case Y3to3
      then show ?thesis
        using Y2to1 S13 S13_in
        unfolding X1' X3'
        by(auto)
    qed
  next
    case Y2to2
    consider (Y3to1) "mdp py3' y3' = mdp px1' x1'" | (Y3to2) "mdp py3' y3' = mdp px2' x2'" | (Y3to3) "mdp py3' y3' = mdp px3' x3'"
      using Y3_cases by auto
    then show ?thesis
    proof cases
      case Y3to1
      have Comm : "{mdp py2' y2', mdp py3' y3'} = {mdp py3' y3', mdp py2' y2'}"
        by auto
      show ?thesis using Y3to1
        using Y2to2 S12 S12_in
        unfolding X1' X2' Comm
        by(auto)
    next
      case Y3to2
      then show ?thesis 
        using Y2to2 X2_dgn X2
        unfolding X2'
        by auto
    next
      case Y3to3
      then show ?thesis
        using Y2to2 S23 S23_in
        unfolding X2' X3'
        by(auto)
    qed
  next
    case Y2to3
    consider (Y3to1) "mdp py3' y3' = mdp px1' x1'" | (Y3to2) "mdp py3' y3' = mdp px2' x2'" | (Y3to3) "mdp py3' y3' = mdp px3' x3'"
      using Y3_cases by auto
    then show ?thesis
    proof cases
      case Y3to1
      have Comm : "{mdp py2' y2', mdp py3' y3'} = {mdp py3' y3', mdp py2' y2'}"
        by auto
      show ?thesis using Y3to1
        using Y2to3 S13 S13_in
        unfolding X1' X3' Comm
        by(auto)
    next
      case Y3to2
      have Comm : "{mdp py2' y2', mdp py3' y3'} = {mdp py3' y3', mdp py2' y2'}"
        by auto
      show ?thesis 
        using Y3to2 Y2to3 S23 S23_in
        unfolding X2' X3' Comm
        by(auto)
    next
      case Y3to3
      then show ?thesis
        using Y2to3 X3_dgn X3
        unfolding X2' X3'
        by(auto)
    qed
  qed
  then obtain sy23 where Sy23 : "is_sup {mdp py2' y2', mdp py3' y3'} sy23" "sy23 \<in> prio_l_S S s"
    by auto

  consider (Y1to1) "mdp py1' y1' = mdp px1' x1'" | (Y1to2) "mdp py1' y1' = mdp px2' x2'" | (Y1to3) "mdp py1' y1' = mdp px3' x3'"
    using Y1_cases by auto
  then have "\<exists> sy13 . is_sup {mdp py1' y1', mdp py3' y3'} sy13 \<and> sy13 \<in> prio_l_S S s"
  proof cases
    case Y1to1
    consider (Y3to1) "mdp py3' y3' = mdp px1' x1'" | (Y3to2) "mdp py3' y3' = mdp px2' x2'" | (Y3to3) "mdp py3' y3' = mdp px3' x3'"
      using Y3_cases by auto
    then show ?thesis
    proof cases
      case Y3to1
      then show ?thesis 
        using Y1to1 X1_dgn X1
        unfolding X1'
        by auto
    next
      case Y3to2
      then show ?thesis 
        using Y1to1 S12 S12_in
        unfolding X1' X2'
        by(auto)
    next
      case Y3to3
      then show ?thesis
        using Y1to1 S13 S13_in
        unfolding X1' X3'
        by(auto)
    qed
  next
    case Y1to2
    consider (Y3to1) "mdp py3' y3' = mdp px1' x1'" | (Y3to2) "mdp py3' y3' = mdp px2' x2'" | (Y3to3) "mdp py3' y3' = mdp px3' x3'"
      using Y3_cases by auto
    then show ?thesis
    proof cases
      case Y3to1
      have Comm : "{mdp py1' y1', mdp py3' y3'} = {mdp py3' y3', mdp py1' y1'}"
        by auto
      show ?thesis using Y3to1
        using Y1to2 S12 S12_in
        unfolding X1' X2' Comm
        by(auto)
    next
      case Y3to2
      then show ?thesis 
        using Y1to2 X2_dgn X2
        unfolding X2'
        by auto
    next
      case Y3to3
      then show ?thesis
        using Y1to2 S23 S23_in
        unfolding X2' X3'
        by(auto)
    qed
  next
    case Y1to3
    consider (Y3to1) "mdp py3' y3' = mdp px1' x1'" | (Y3to2) "mdp py3' y3' = mdp px2' x2'" | (Y3to3) "mdp py3' y3' = mdp px3' x3'"
      using Y3_cases by auto
    then show ?thesis
    proof cases
      case Y3to1
      have Comm : "{mdp py1' y1', mdp py3' y3'} = {mdp py3' y3', mdp py1' y1'}"
        by auto
      show ?thesis using Y3to1
        using Y1to3 S13 S13_in
        unfolding X1' X3' Comm
        by(auto)
    next
      case Y3to2
      have Comm : "{mdp py1' y1', mdp py3' y3'} = {mdp py3' y3', mdp py1' y1'}"
        by auto
      show ?thesis 
        using Y3to2 Y1to3 S23 S23_in
        unfolding X2' X3' Comm
        by(auto)
    next
      case Y3to3
      then show ?thesis
        using Y1to3 X3_dgn X3
        unfolding X2' X3'
        by(auto)
    qed
  qed

  then obtain sy13 where Sy13 : "is_sup {mdp py1' y1', mdp py3' y3'} sy13" "sy13 \<in> prio_l_S S s"
    by auto

  show "s123 \<in> prio_l_S S s"
  proof(cases "py2' < py3'")
    case Lt23 : True
    then have "is_sup {mdp py1' y1', mdp py2' y2', mdp py3' y3'} (mdp py3' y3')"
      using Ys(2) Ys(3)
      by(auto simp add: is_sup_def is_least_def is_ub_def prio_pleq leq_refl)

    then have "s123 = mdp py3' y3'"
      using is_sup_unique[OF S123]
      unfolding X1' X2' X3' Ys(1)
      by auto

    then show ?thesis using Y3_in
      by auto
  next
    case False
    then have Eq23 : "py2' = py3'"
      using Ys(3) by auto

    show ?thesis
    proof(cases "py1' < py2'")
      case Lt12 : True

      have "is_sup {mdp py1' y1', mdp py2' y2', mdp py3' y3'} (sy23)"
      proof(rule is_supI)
        fix x
        assume "x \<in> {mdp py1' y1', mdp py2' y2', mdp py3' y3'}"
        then consider (1) "x = mdp py1' y1'" | (2) "x = mdp py2' y2'" | (3) "x = mdp py3' y3'"
          by auto
        then show "x <[ sy23"
        proof cases
          case 1

          have Leq1: "mdp py1' y1' <[ mdp py2' y2'"
            using Lt12
            by(auto simp add: prio_pleq)

          have Leq2 : "mdp py2' y2' <[ sy23"
            using is_supD1[OF Sy23(1), of "mdp py2' y2'"]
            by auto

          then show ?thesis using leq_trans[OF Leq1 Leq2] 1
            by auto
        next
          case 2
          then show ?thesis using is_supD1[OF Sy23(1)]
            by auto
        next
          case 3
          then show ?thesis using is_supD1[OF Sy23(1)]
            by auto
        qed
      next
        fix w

        assume Ub : "is_ub {mdp py1' y1', mdp py2' y2', mdp py3' y3'} w"

        then have Ub' : "is_ub {mdp py2' y2', mdp py3' y3'} w"
          by(auto simp add: is_ub_def)

        show "sy23 <[ w" using is_supD2[OF Sy23(1) Ub']
          by auto
      qed

      then have "s123 = sy23"
        using is_sup_unique[OF S123]
        unfolding X1' X2' X3' Ys(1)
        by auto
  
      then show ?thesis using Sy23(2)
        by auto
    next
      case False
      then have Eq12 : "py1' = py2'"
        using Ys(2) by auto

      show ?thesis
      proof(cases "has_sup {y1', y2'}")
        case Y1'Y2'_NoSup : False

        have Bump : "is_sup {mdp py1' y1', mdp py2' y2'} (mdp (1 + py1') \<bottom>)" 
          using prio_sup_overflow[OF Y1'Y2'_NoSup Eq12]
          by auto

        then have "mdp (1 + py1') \<bottom> = sy12"
          using is_sup_unique[OF Sy12(1) Bump]
          by auto

        then have Sup_In : "(mdp (1 + py1') \<bottom>) \<in> prio_l_S S s"
          using Sy12(2)
          by auto

        have Conc' : "is_sup {mdp py1' y1', mdp py2' y2', mdp py3' y3'} (mdp (1 + py1') \<bottom>)"
        proof(rule is_supI)
          fix x
          assume "x \<in> {mdp py1' y1', mdp py2' y2', mdp py3' y3'}"
          then show "x <[ (mdp (1 + py1') \<bottom>)"
            using Eq12 Eq23
            by(auto simp add: prio_pleq)
        next
          fix w

          assume Ub : "is_ub {mdp py1' y1', mdp py2' y2', mdp py3' y3'} w"

          obtain pw' w' where W : "w = mdp pw' w'"
            by(cases w; auto)

          have Leq : "py1' \<le> pw'"
            using is_ubE[OF Ub, of "mdp py1' y1'"] W
            by(auto simp add: prio_pleq split: if_splits)

          then show "mdp (1 + py1') \<bottom> <[ w"
          proof(cases "py1' = pw'")
            case True

            then have "is_ub {y1', y2'} w'"
              using Ub W Eq12
              by(auto simp add: is_ub_def prio_pleq split: if_splits)

            then have "has_sup {y1', y2'}"
              using complete2
              by(auto simp add: has_ub_def)

            then have False using Y1'Y2'_NoSup
              by auto

            then show ?thesis by auto
          next
            case False
            then have "py1' < pw'" using Leq by auto
            then show ?thesis
              using W
              by(auto simp add: prio_pleq bot_spec)
          qed
        qed

        then have Conc_Eq : "s123 = (mdp (1 + py1') \<bottom>)"
          using is_sup_unique[OF S123]
          unfolding X1' X2' X3' Ys(1)
          by auto

        then show ?thesis using Sup_In by auto
      next
        case Y1'Y2'_Sup : True 
        show ?thesis
        proof(cases "has_sup {y2', y3'}")
          case Y2'Y3'_NoSup : False
  
          have Bump : "is_sup {mdp py2' y2', mdp py3' y3'} (mdp (1 + py1') \<bottom>)" 
            using prio_sup_overflow[OF Y2'Y3'_NoSup Eq23] Eq12
            by auto
  
          then have "mdp (1 + py1') \<bottom> = sy23"
            using is_sup_unique[OF Sy23(1) Bump]
            by auto
  
          then have Sup_In : "(mdp (1 + py1') \<bottom>) \<in> prio_l_S S s"
            using Sy23(2)
            by auto
  
          have Conc' : "is_sup {mdp py1' y1', mdp py2' y2', mdp py3' y3'} (mdp (1 + py1') \<bottom>)"
          proof(rule is_supI)
            fix x
            assume "x \<in> {mdp py1' y1', mdp py2' y2', mdp py3' y3'}"
            then show "x <[ (mdp (1 + py1') \<bottom>)"
              using Eq12 Eq23
              by(auto simp add: prio_pleq)
          next
            fix w
  
            assume Ub : "is_ub {mdp py1' y1', mdp py2' y2', mdp py3' y3'} w"
  
            obtain pw' w' where W : "w = mdp pw' w'"
              by(cases w; auto)
  
            have Leq : "py1' \<le> pw'"
              using is_ubE[OF Ub, of "mdp py1' y1'"] W
              by(auto simp add: prio_pleq split: if_splits)
  
            then show "mdp (1 + py1') \<bottom> <[ w"
            proof(cases "py1' = pw'")
              case True
  
              then have "is_ub {y2', y3'} w'"
                using Ub W Eq12 Eq23
                by(auto simp add: is_ub_def prio_pleq split: if_splits)
  
              then have "has_sup {y2', y3'}"
                using complete2
                by(auto simp add: has_ub_def)
  
              then have False using Y2'Y3'_NoSup
                by auto
  
              then show ?thesis by auto
            next
              case False
              then have "py1' < pw'" using Leq by auto
              then show ?thesis
                using W
                by(auto simp add: prio_pleq bot_spec)
            qed
          qed
  
          then have Conc_Eq : "s123 = (mdp (1 + py1') \<bottom>)"
            using is_sup_unique[OF S123]
            unfolding X1' X2' X3' Ys(1)
            by auto
  
          then show ?thesis using Sup_In by auto
        next
          case Y2'Y3'_Sup : True 
          show ?thesis
          proof(cases "has_sup {y1', y3'}")
            case Y1'Y3'_NoSup : False
    
            have Bump : "is_sup {mdp py1' y1', mdp py3' y3'} (mdp (1 + py1') \<bottom>)" 
              using prio_sup_overflow[OF Y1'Y3'_NoSup Eq23] Eq12
              by auto
    
            then have "mdp (1 + py1') \<bottom> = sy13"
              using is_sup_unique[OF Sy13(1) Bump]
              by auto
    
            then have Sup_In : "(mdp (1 + py1') \<bottom>) \<in> prio_l_S S s"
              using Sy13(2)
              by auto
    
            have Conc' : "is_sup {mdp py1' y1', mdp py2' y2', mdp py3' y3'} (mdp (1 + py1') \<bottom>)"
            proof(rule is_supI)
              fix x
              assume "x \<in> {mdp py1' y1', mdp py2' y2', mdp py3' y3'}"
              then show "x <[ (mdp (1 + py1') \<bottom>)"
                using Eq12 Eq23
                by(auto simp add: prio_pleq)
            next
              fix w
    
              assume Ub : "is_ub {mdp py1' y1', mdp py2' y2', mdp py3' y3'} w"
    
              obtain pw' w' where W : "w = mdp pw' w'"
                by(cases w; auto)
    
              have Leq : "py1' \<le> pw'"
                using is_ubE[OF Ub, of "mdp py1' y1'"] W
                by(auto simp add: prio_pleq split: if_splits)
    
              then show "mdp (1 + py1') \<bottom> <[ w"
              proof(cases "py1' = pw'")
                case True
    
                then have "is_ub {y1', y3'} w'"
                  using Ub W Eq12 Eq23
                  by(auto simp add: is_ub_def prio_pleq split: if_splits)
    
                then have "has_sup {y1', y3'}"
                  using complete2
                  by(auto simp add: has_ub_def)
    
                then have False using Y1'Y3'_NoSup
                  by auto
    
                then show ?thesis by auto
              next
                case False
                then have "py1' < pw'" using Leq by auto
                then show ?thesis
                  using W
                  by(auto simp add: prio_pleq bot_spec)
              qed
            qed
    
            then have Conc_Eq : "s123 = (mdp (1 + py1') \<bottom>)"
              using is_sup_unique[OF S123]
              unfolding X1' X2' X3' Ys(1)
              by auto
    
            then show ?thesis using Sup_In by auto
          next
            case Y1'Y3'_Sup : True

            have Y1'_in : "y1' \<in> S s"
              using Y1_in by(auto simp add: prio_l_S_def)
            have Y2'_in : "y2' \<in> S s"
              using Y2_in by(auto simp add: prio_l_S_def)            
            have Y3'_in : "y3' \<in> S s"
              using Y3_in by(auto simp add: prio_l_S_def)

            obtain sup_inner_12 where Inner_12 : "is_sup {y1', y2'} sup_inner_12"
              using Y1'Y2'_Sup
              by(auto simp add: has_sup_def)

            have Inner_12_eq : "sy12 = mdp py1' sup_inner_12"
              using is_sup_unique[OF Sy12(1)] prio_sup_inner[OF Inner_12 Eq12]
              by auto

            then have Inner_12_in : "sup_inner_12 \<in> S s"
              using Sy12(2)
              by (auto simp add: prio_l_S_def)

            obtain sup_inner_23 where Inner_23 : "is_sup {y2', y3'} sup_inner_23"
              using Y2'Y3'_Sup
              by(auto simp add: has_sup_def)

            have Inner_23_eq : "sy23 = mdp py1' sup_inner_23"
              using is_sup_unique[OF Sy23(1)] prio_sup_inner[OF Inner_23 Eq23] Eq12
              by auto

            then have Inner_23_in : "sup_inner_23 \<in> S s"
              using Sy23(2)
              by (auto simp add: prio_l_S_def)

            obtain sup_inner_13 where Inner_13 :"is_sup {y1', y3'} sup_inner_13"
              using Y1'Y3'_Sup
              by(auto simp add: has_sup_def)

            have Eq13 : "py1' = py2'"
              using Eq12 Eq23
              by auto

            have Inner_13_eq : "sy13 = mdp py1' sup_inner_13"
              using is_sup_unique[OF Sy13(1)] prio_sup_inner[OF Inner_13 Eq13] Eq12 Eq23
              by auto

            then have Inner_13_in : "sup_inner_13 \<in> S s"
              using Sy13(2)
              by (auto simp add: prio_l_S_def)

            obtain sup_inner_123 where Inner_123 : "is_sup {y1', y2', y3'} sup_inner_123"
              using pairwise_sup[OF Y1'Y2'_Sup Y2'Y3'_Sup Y1'Y3'_Sup]
              by(auto simp add: has_sup_def)

            have Inner_123_in : "sup_inner_123 \<in> S s"
              using pairwise_S[OF Y1'_in Y2'_in Y3'_in Inner_12 Inner_12_in Inner_23 Inner_23_in Inner_13 Inner_13_in Inner_123]
              by auto

            have Inner_123_Full_Sup : "is_sup {mdp py1' y1', mdp py1' y2', mdp py1' y3'} (mdp py1' sup_inner_123)"
            proof(rule is_supI)
              fix x
              assume "x \<in> {mdp py1' y1', mdp py1' y2', mdp py1' y3'}"

              then show "x <[ mdp py1' sup_inner_123"
                using is_supD1[OF Inner_123, of y1'] is_supD1[OF Inner_123, of y2'] is_supD1[OF Inner_123, of y3']
                by(cases x; auto simp add: prio_pleq split:if_splits)
            next
              fix w

              assume Ub : "is_ub {mdp py1' y1', mdp py1' y2', mdp py1' y3'} w"

              obtain pw' w' where W : "w = mdp pw' w'"
                by(cases w; auto)
    
              have Leq : "py1' \<le> pw'"
                using is_ubE[OF Ub, of "mdp py1' y1'"] W
                by(auto simp add: prio_pleq split: if_splits)
    
              then show "mdp py1' sup_inner_123 <[ w"
              proof(cases "py1' = pw'")
                case True
    
                then have "is_ub {y1', y2', y3'} w'"
                  using Ub W Eq12 Eq23
                  by(auto simp add: is_ub_def prio_pleq split: if_splits)

                then have "sup_inner_123 <[ w'"
                  using is_supD2[OF Inner_123]
                  by auto
    
                then show ?thesis using W True
                  by(auto simp add: prio_pleq)
              next
                case False
                then have "py1' < pw'" using Leq by auto
                then show ?thesis
                  using W
                  by(auto simp add: prio_pleq bot_spec)
              qed
            qed
    
            then have Conc_Eq : "s123 = (mdp py1' sup_inner_123)"
              using is_sup_unique[OF S123]
              unfolding X1' X2' X3' Ys(1) Eq12 Eq23
              by auto
    
            then show ?thesis using Inner_123_in
              by(auto simp add: prio_l_S_def)
          qed
        qed
      qed
    qed
  qed
qed


lemma (in prio_l_valid_pairwise_ext) ax :
  shows "lifting_valid_pairwise_ext (prio_l_S S)"
  using out.lifting_valid_pairwise_ext_axioms
  by auto

lemma (in prio_l_valid_pairwise_ext) ax_g :
  assumes H : "\<And> x . S' x = prio_l_S S x"
  shows "lifting_valid_pairwise_ext S'"
proof-
  have "S' = prio_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_pairwise_ext_axioms assms
  by auto
qed

(* NB: "stronger" version of prio_l does not work with pres, because we need to know that
 * we are actually in prio_l_S S, not some superset.
 *)

(* Several useful examples of instantiating prio_l.
*)
definition prio_l_keep :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_keep =
  prio_l (\<lambda> _ . 0) (\<lambda> _ n . n)"

definition prio_l_inc :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 1 + x)"

definition prio_l_inc2 :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc2 =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 2 + x)"

definition prio_l_inc3 :: "('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_inc3 =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 3  + x)"

definition prio_l_incN :: "nat \<Rightarrow> ('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_incN n =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . n + x)"

definition prio_l_case_inc :: "('x \<Rightarrow> nat) \<Rightarrow> ('x, 'a, 'b :: Pord) lifting \<Rightarrow> ('x, 'a, 'b md_prio) lifting" where
"prio_l_case_inc f =
  prio_l (\<lambda> _ . 0) (\<lambda> s x . (f s) + x)"

(* Prio - let's defer this until later as we may not need it.
 * my guess is it's true, but annoying. *)

(*
locale prio_l_ortho = l_ortho (* ... *)

locale prio_l_ortho_pres_ext = l_ortho_pres_ext (* ... *)

locale prio_l_ortho_base_ext = l_ortho_base_ext (* ... *)

locale prio_l_ortho_ok_ext = l_ortho_ok_ext (* ... *)
*)

(* next, products:
- ortho between fst and fst, if inner liftings ortho
- snd and snd, ditto
- fst and snd, unconditionally
*)


end