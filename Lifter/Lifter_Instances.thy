theory Lifter_Instances imports Lifter "../Mergeable/Mergeable_Facts" "../Mergeable/Wrappers" "../Mergeable/Mergeable_Instances"
begin

instantiation oalist :: (linorder, _) Bogus begin
definition oalist_bogus : "bogus = (empty :: (_, _) oalist)"
instance proof qed
end


(* TODO: add VSG versions of these, and hopefully
   figure out a way to infer. *)
(*
 * id
 *)
definition id_l ::
  "('x, 'a :: {Pord, Bogus}, 'a) lifting" where
"id_l =
  LMake (\<lambda> s a a' . a) (\<lambda> s a . a) (\<lambda> s . bogus)" 

interpretation id_l: lifting_valid_weak "id_l" "\<lambda> _ . UNIV"
proof
  show "\<And>s a b. LOut id_l s (LUpd id_l s a b) = a"
    by(auto simp add: id_l_def)
next
  show "\<And>s b. b \<in> UNIV \<Longrightarrow>
           b <[ LUpd id_l s (LOut id_l s b) b"
    by(auto simp add: id_l_def leq_refl)
next
  show "\<And>s a b. LUpd id_l s a b \<in> UNIV"
    by auto
qed

(*
 * triv
 *)
definition triv_l ::
  "('x, 'a :: Bogus, 'a md_triv) lifting" where
"triv_l =
  LMake (\<lambda> s a _ . mdt a) (\<lambda> s b . (case b of (mdt b') \<Rightarrow> b')) (\<lambda> s . mdt bogus)"

interpretation triv_l : 
  lifting_valid_weak "(triv_l :: ('x, 'a :: Bogus, 'a md_triv) lifting)" "\<lambda> _ . UNIV"
proof
  fix s :: 'x
  fix a :: 'a
  fix b
  show "LOut (triv_l) s (LUpd (triv_l) s a b) = a"
    by(auto simp add:triv_l_def split:md_triv.splits)
next
  fix s :: 'x
  fix b :: "'a md_triv"

  show "b <[ LUpd triv_l s (LOut triv_l s b) b"
   by(auto simp add:triv_l_def triv_pleq
          split:md_triv.splits)
next
  fix s :: 'x
  fix a :: "'a"
  fix b :: "'a md_triv"
  show "LUpd triv_l s a b \<in> UNIV" by auto
qed


interpretation triv_l:
  lifting_valid_ok_ext "(triv_l :: ('x, 'a :: {Bogus, Okay}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
  show "\<And> S . ok_S \<subseteq> UNIV" by auto
next
  fix s a b
  show "b \<in> ok_S \<Longrightarrow> LUpd triv_l s a b \<in> ok_S"
    by(auto simp add: triv_l_def triv_ok_S)
qed


interpretation triv_l :
  lifting_valid_pres_ext "(triv_l :: ('x, 'a :: {Bogus}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
next
  fix v :: "'a md_triv"
  fix V 
  fix supr :: "'a md_triv"
  fix s 
  fix f

  assume Nemp : "v \<in> V"
  assume H : "is_sup V supr"

  show "is_sup (LMap triv_l f s ` V) (LMap triv_l f s supr)"
  proof(rule is_supI)
    fix x

    assume "x \<in> LMap triv_l f s ` V"

    then obtain x0 where X0 : "x0 \<in> V" "LMap triv_l f s x0 = x"
      by(auto)

    obtain x0' where X0' : "x0 = mdt x0'"
      by(cases x0; auto)

    obtain supr' where Supr' : "supr = mdt supr'"
      by(cases supr; auto)

    have Eq : "x0' = supr'"
      using is_supD1[OF H X0(1)] X0' Supr'
      by(auto simp add: triv_pleq)

    show "x <[ LMap triv_l f s supr"
      using X0' X0 Eq Supr'
      by(auto simp add: triv_pleq)
  next
    fix y
    assume Ub : "is_ub (LMap triv_l f s ` V) y"

    obtain y' where Y' : "y = mdt y'" by(cases y; auto)

    obtain v' where V' : "v = mdt v'" by(cases v; auto)

    have Eq1 : "y = LMap triv_l f s v"
      using is_ubE[OF Ub, of "LMap triv_l f s v"] Nemp
      by(auto simp add: triv_pleq)

    have  "supr = v"
      using is_supD1[OF H Nemp] by(auto simp add: triv_pleq)

    hence Eq2 : "LMap triv_l f s supr = LMap triv_l f s v" by simp

    show "LMap triv_l f s supr <[ y"
      using Eq1 Eq2
      by(simp add: triv_pleq)
  qed
qed

(*
interpretation triv_l : lifting_valid_weak_ok_pres "(triv_l :: ('x, 'a :: {Bogus, Okay}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
qed
*)
interpretation triv_l : lifting_valid_pairwise_ext "\<lambda> _ . (UNIV :: 'a md_triv set)"
proof
  fix x1 x2 x3 s12 s23 s13 s123 :: "'a md_triv"

  show "s123 \<in> UNIV"
    by auto
qed


(*
 * option
 *)
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

definition option_l_S :: "('s, 'b) valid_set \<Rightarrow> ('s, 'b option) valid_set" where
"option_l_S S s = (Some ` S s)"


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

lemma is_sup_pair :
  assumes "a <[ b"
  shows "is_sup {a, b} b" using assms
  by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

(*
locale option_l_valid_weak_grade =
  option_l_valid_weak + lifting_valid_weak_grade
*)
(*
sublocale option_l_valid_weak_grade \<subseteq> out : lifting_valid_weak_grade "option_l l" "option_l_S S"
proof
  fix a b :: 'b
  fix x1 x2 :: "'c option"
  fix s
  assume "x1 \<in> option_l_S S s"
  then obtain x1' where X1 : "x1' \<in> S s" "x1 = Some x1'"
    by(cases x1; auto simp add: option_l_S_def)
  assume "x2 \<in> option_l_S S s"
  then obtain x2' where X2 : "x2' \<in> S s" "x2 = Some x2'"
    by(cases x2; auto simp add: option_l_S_def)

  assume "x1 <[ x2"
  then have Leq' : "x1' <[ x2'"
    using X1 X2
    by(auto simp add: option_pleq)

  assume "LOut (option_l l) s x1 = LOut (option_l l) s x2"
  then have Out_eq : "LOut l s x1' = LOut l s x2'"
    using X1 X2
    by(auto simp add: option_l_def)

  assume "x1 \<noteq> x2"
  then have Neq : "x1' \<noteq> x2'"
    using X1 X2
    by auto

  have Conc' : "LUpd l s a x1' <[ LUpd l s b x2'"
    using graded[OF X1(1) X2(1) Leq' Out_eq Neq]
    by auto

  then show 
    "LUpd (option_l l) s a x1 <[ LUpd (option_l l) s b x2"
    using X1 X2
    by(auto simp add: option_l_def option_pleq)
qed
*)

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

locale prio_l_valid_stronger = prio_l_valid_strong + prio_l_valid_ext_stronger'
sublocale prio_l_valid_stronger \<subseteq> out : lifting_valid "prio_l f0 f1 l" "T"
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

lemma (in prio_l_valid_stronger) ax :
  shows "lifting_valid (prio_l f0 f1 l) T"
  using out.lifting_valid_weak_axioms out.lifting_valid_ext_axioms
  by(intro_locales; auto)

lemma (in prio_l_valid_stronger) ax_g :
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

locale prio_l_valid_stronger_ok = prio_l_valid_weak_ok + prio_l_valid_stronger

sublocale prio_l_valid_stronger_ok \<subseteq> out : lifting_valid_ok "prio_l f0 f1 l" "T"
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

lemma (in prio_l_valid_stronger_ok) ax :
  shows "lifting_valid_ok_ext (prio_l f0 f1 l) T"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in prio_l_valid_stronger_ok) ax_g :
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

(*
  consider (C123) "px1' \<le> px2'" "px2' \<le> px3'" |
           (C132) "px1' \<le> px3'" "px3' \<le> px2'" |
           (C213) "px2' \<le> px1'" "px1' \<le> px3'" |
           (C231) "px2' \<le> px3'" "px3' \<le> px1'" |
           (C312) "px3' \<le> px1'" "px1' \<le> px2'" |
           (C321) "px3' \<le> px2'" "px2' \<le> px1'"
    by(arith)

  then show "s123 \<in> prio_l_S S s"
  proof cases
    case C123

    then consider (Eq23) "px2' = px3'" | (Lt23) "px2' < px3'"
      by arith

    then show ?thesis
    proof cases
      case Eq23

      then consider (Eq12) "px1' = px2'" | (Lt12) "px1' < px2'"
        using C123
        by arith

      then show ?thesis
      proof cases
        case Eq12
        then show ?thesis
          consider (Found12) "
          
          sorry
      next
        case Lt12
        then show ?thesis sorry
      qed
    next
      case Lt23
      then show ?thesis sorry
    qed
  next
    case C132
    then show ?thesis sorry
  next
    case C213
    then show ?thesis sorry
  next
    case C231
    then show ?thesis sorry
  next
  case C312
    then show ?thesis sorry
  next
    case C321
  then show ?thesis sorry
  qed
*)
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

(*
 * fst
 *)

definition fst_l ::
  "('x, 'a, 'b1 :: Pord_Weak) lifting \<Rightarrow>
   ('x, 'a, 'b1 * ('b2 :: Pord_Weakb)) lifting" where
"fst_l t =
  LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (LUpd t s a b1, b2)))
            (\<lambda> s x . (LOut t s (fst x)))
            (\<lambda> s . (LBase t s, \<bottom>))"

definition fst_l_S :: "('x, 'b1 :: Pord_Weak) valid_set \<Rightarrow> ('x, ('b1 * 'b2 :: Pord_Weakb)) valid_set" where
"fst_l_S S s =
  { b . case b of (b1, _) \<Rightarrow> (b1 \<in> S s) }"

locale fst_l_valid_weak = lifting_valid_weak

sublocale fst_l_valid_weak \<subseteq> out:lifting_valid_weak "fst_l l" "fst_l_S S"
proof
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  show "LOut (fst_l l) s (LUpd (fst_l l) s a b) = a"
    using put_get
    by(auto simp add: fst_l_def split:prod.splits)
next
  fix s
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  assume  Hb : "b \<in> fst_l_S S s"
  thus "b <[ LUpd (fst_l l) s (LOut (fst_l l) s b) b"
    using get_put_weak
    by(auto simp add: fst_l_def prod_pleq leq_refl fst_l_S_def split:prod.splits)
next
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  show "LUpd (fst_l l) s a b \<in> fst_l_S S s"
    using put_S
    by(auto simp add: fst_l_def prod_pleq leq_refl fst_l_S_def split:prod.splits)
qed

lemma (in fst_l_valid_weak) ax:
  shows "lifting_valid_weak (fst_l l) (fst_l_S S)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in fst_l_valid_weak) ax_g :
  assumes H : "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_weak (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_weak_axioms assms
    by auto
qed

locale fst_l_valid_ext = lifting_valid_ext

sublocale fst_l_valid_ext \<subseteq> out : lifting_valid_ext "fst_l l" "fst_l_S S"
proof
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  (*assume  Hb : "b \<in> fst_l_S S s"*)
  show "b <[ LUpd (fst_l l) s a b"
    using get_put
    by(auto simp add: fst_l_def prod_pleq fst_l_S_def leq_refl split:prod.splits)
qed

lemma (in fst_l_valid_ext) ax:
  shows "lifting_valid_ext (fst_l l)"
  using out.lifting_valid_ext_axioms
  by auto

locale fst_l_valid_base_ext = lifting_valid_base_ext

sublocale fst_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "fst_l l" "fst_l_S S"
proof
  fix s
  show "LBase (fst_l l) s = \<bottom>" using base
    by(auto simp add: fst_l_def prod_bot)
qed

lemma (in fst_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (fst_l l)"
  using out.lifting_valid_base_ext_axioms
  by auto

locale fst_l_valid_ok_ext = lifting_valid_ok_ext
sublocale fst_l_valid_ok_ext \<subseteq> out : lifting_valid_ok_ext "fst_l l" "fst_l_S S"
proof
  fix s

  show "ok_S \<subseteq> fst_l_S S s" using ok_S_valid
    by(auto simp add: prod_ok_S fst_l_S_def)
next
  fix s a
  fix b :: "('c * 'd)"
  assume B: "b \<in> ok_S" 
  then show "LUpd (fst_l l) s a b \<in> ok_S" using ok_S_put
    by(auto simp add: fst_l_def prod_ok_S)
qed

lemma (in fst_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (fst_l l) (fst_l_S S)"
  using out.lifting_valid_ok_ext_axioms by auto

lemma (in fst_l_valid_ok_ext) ax_g :
  assumes H: "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_ok_ext (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_ok_ext_axioms assms 
    by auto
qed

locale fst_l_valid_pres_ext = lifting_valid_pres_ext
sublocale fst_l_valid_pres_ext \<subseteq> out : lifting_valid_pres_ext "fst_l l" "fst_l_S S"
proof
  fix v supr :: "('c * 'd)"
  fix V f s

  assume HV : "v \<in> V"
  assume HS : "V \<subseteq> fst_l_S S s"
  assume Hsupr : "is_sup V supr"
  assume Hsupr_S : "supr \<in> fst_l_S S s"
  show "is_sup (LMap (fst_l l) f s ` V) (LMap (fst_l l) f s supr)"
  proof(rule is_supI)

    fix x

    assume Xin : "x \<in> LMap (fst_l l) f s ` V"

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    obtain xi xi1 xi2 where Xi : "xi = (xi1, xi2)" "xi \<in> V" "LMap (fst_l l) f s xi = x"
      using Xin
      by auto

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

    have "xi <[ supr" using is_supD1[OF Hsupr Xi(2)] by simp

    hence "xi1 <[ supr1" "xi2 <[ supr2"
      using Xi Supr
      by(auto simp add: prod_pleq split: prod.splits)

    have "x2 = xi2" using Xi X
      by(cases l; auto simp add: fst_l_def)

    have "x1 = LMap l f s xi1"
      using Xi X
      by(cases l; auto simp add: fst_l_def)

    have "LMap (fst_l l) f s supr = (LMap l f s supr1, supr2)"
      using Supr
      by(cases l; auto simp add: fst_l_def)

    have Xi1_in : "xi1 \<in> fst ` V"
      using imageI[OF `xi \<in> V`, of fst] Xi
      by(auto simp add: fst_l_S_def)

    have Fst_V_sub : "fst ` V \<subseteq> S s"
      using HS
      by(auto simp add: fst_l_S_def)

    have "supr1 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: fst_l_S_def)

    have Supr1_sup : "is_sup (fst ` V) supr1"
    proof(rule is_supI)
      fix w1
      assume "w1 \<in> fst ` V"

      then obtain w2 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w1 <[ supr1" using Supr by(auto simp add: prod_pleq)
    next

      fix z1

      assume Hub : "is_ub (fst ` V) z1"

      have "is_ub V (z1, supr2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w1 \<in> (fst ` V)"
          using imageI[OF `w \<in> V`, of fst] W by auto

        hence "w1 <[ z1" using is_ubE[OF Hub] by auto

        have "w2 <[ supr2" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (z1, supr2)" using W `w1 <[ z1`
          by(auto simp add: prod_pleq)
      qed

      show "supr1 <[ z1"
        using is_supD2[OF Hsupr `is_ub V (z1, supr2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    have Supr1_map : "is_sup (LMap l f s ` fst ` V) (LMap l f s supr1)"
      using pres using pres[OF Xi1_in Fst_V_sub Supr1_sup `supr1 \<in> S s` , of f]
      by simp

    have X1_in : "x1 \<in> LMap l f s ` fst ` V"
      using X Xi imageI[OF `xi \<in> V`, of fst]
      by(cases l; auto simp add: fst_l_def)

    have "x1 <[ LMap l f s supr1"
      using is_supD1[OF Supr1_map X1_in]
      by simp

    have "x2 <[ supr2" using `x2 = xi2` `xi2 <[ supr2` by simp

    then show "x <[ LMap (fst_l l) f s supr"
      using X Supr `x1 <[ LMap l f s supr1`
      by(cases l; auto simp add: fst_l_def prod_pleq)
  next
    fix x

    assume Xub : "is_ub (LMap (fst_l l) f s ` V) x"

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

  (* TODO: copy-pasted from first case *)
    have "LMap (fst_l l) f s supr = (LMap l f s supr1, supr2)"
      using Supr
      by(cases l; auto simp add: fst_l_def)

    have Fst_V_sub : "fst ` V \<subseteq> S s"
      using HS
      by(auto simp add: fst_l_S_def)

    have "supr1 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: fst_l_S_def)

    have Supr1_sup : "is_sup (fst ` V) supr1"
    proof(rule is_supI)
      fix w1
      assume "w1 \<in> fst ` V"

      then obtain w2 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w1 <[ supr1" using Supr by(auto simp add: prod_pleq)
    next

      fix z1

      assume Hub : "is_ub (fst ` V) z1"

      have "is_ub V (z1, supr2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w1 \<in> (fst ` V)"
          using imageI[OF `w \<in> V`, of fst] W by auto

        hence "w1 <[ z1" using is_ubE[OF Hub] by auto

        have "w2 <[ supr2" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (z1, supr2)" using W `w1 <[ z1`
          by(auto simp add: prod_pleq)
      qed

      show "supr1 <[ z1"
        using is_supD2[OF Hsupr `is_ub V (z1, supr2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    obtain v1 v2 where V : "v = (v1, v2)" "v1 \<in> fst ` V"
      using imageI[OF HV, of fst]
      by(cases v; auto)

    have Supr1_map : "is_sup (LMap l f s ` fst ` V) (LMap l f s supr1)"
      using pres[OF V(2) Fst_V_sub Supr1_sup `supr1 \<in> S s` ] 
      by simp

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    have X1_ub : "is_ub (LMap l f s ` fst ` V) x1"
    proof
      fix w1

      assume W1: "w1 \<in> LMap l f s ` fst ` V"

      then obtain wi wi1 wi2  where Wi : "wi \<in> V" "LMap l f s wi1 = w1" "wi = (wi1, wi2)"
        by(auto)

      have Wi_in : "LMap (fst_l l) f s wi \<in> LMap (fst_l l) f s ` V"
        using imageI[OF Wi(1), of "LMap (fst_l l) f s"] by simp

      have "LMap (fst_l l) f s wi <[ x"
        using is_ubE[OF Xub Wi_in]
        by simp

      then show "w1 <[ x1"
        using W1 Wi X
        by(cases l; auto simp add: prod_pleq fst_l_def)
    qed  

    have "LMap l f s supr1 <[ x1"
      using is_supD2[OF Supr1_map X1_ub]
      by simp

    have "is_ub V (supr1, x2)"
    proof(rule is_ubI)
      fix w

      assume Win : "w \<in> V"

      obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

      have W1_in : "w1 \<in> fst ` V"
        using imageI[OF Win, of fst] W by simp

      have "w1 <[ supr1"
        using is_supD1[OF Supr1_sup W1_in] by simp

      have "LMap (fst_l l) f s w <[ x"
        using is_ubE[OF Xub imageI[OF Win]] by simp

      hence "w2 <[ x2" using W X
        by(cases l; auto simp add: fst_l_def prod_pleq)

      show "w <[ (supr1, x2)"
        using `w1 <[ supr1` `w2 <[ x2` W
        by(auto simp add: prod_pleq)
    qed

    have "supr2 <[ x2"
      using is_supD2[OF Hsupr `is_ub V (supr1, x2)`] Supr
      by(auto simp add: prod_pleq)


    show "LMap (fst_l l) f s supr <[ x"
      using `LMap l f s supr1 <[ x1` `supr2 <[ x2` X Supr
      by(cases l; auto simp add: fst_l_def prod_pleq)
  qed
qed

lemma (in fst_l_valid_pres_ext) ax :
  shows "lifting_valid_pres_ext (fst_l l) (fst_l_S S)"
  using out.lifting_valid_pres_ext_axioms
  by auto

lemma (in fst_l_valid_pres_ext) ax_g :
  assumes H: "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_pres_ext (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_pres_ext_axioms
    by auto
qed

locale fst_l_valid_base_pres_ext = fst_l_valid_pres_ext + fst_l_valid_base_ext + lifting_valid_base_pres_ext

sublocale fst_l_valid_base_pres_ext \<subseteq> out : lifting_valid_base_pres_ext "fst_l l" "fst_l_S S"
proof
  fix s
  show "\<bottom> \<notin> fst_l_S S s"
    using bot_bad[of s]
    by(auto simp add: fst_l_S_def prod_bot)
qed

lemma (in fst_l_valid_base_pres_ext) ax :
  shows "lifting_valid_base_pres_ext (fst_l l) (fst_l_S S)"
  using out.lifting_valid_base_pres_ext_axioms
  by auto

lemma (in fst_l_valid_base_pres_ext) ax_g :
  assumes H : "\<And> x . S' x = fst_l_S S x"
  shows "lifting_valid_base_pres_ext (fst_l l) S'"
proof-
  have "S' = fst_l_S S" using assms by auto
  then show ?thesis using out.lifting_valid_base_pres_ext_axioms
    by auto
qed

(*
 * snd
 *)

definition snd_l ::
  "('x, 'a, 'b2 :: Pord_Weak) lifting \<Rightarrow>
   ('x, 'a, ('b1 :: Pord_Weakb) * 'b2) lifting" where
"snd_l t =
      LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (b1, LUpd t s a b2)))
            (\<lambda> s x . (LOut t s (snd x)))
            (\<lambda> s . (\<bottom>, LBase t s))"

definition snd_l_S :: "('x, 'b2 :: Pord_Weak) valid_set \<Rightarrow> ('x, ('b1 :: Pord_Weakb * 'b2)) valid_set" where
"snd_l_S S s =
  { b . case b of (_, b2) \<Rightarrow> (b2 \<in> S s) }"


locale snd_l_valid_weak = lifting_valid_weak

sublocale snd_l_valid_weak \<subseteq> out : lifting_valid_weak "snd_l l" "snd_l_S S"
proof
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  show "LOut (snd_l l) s (LUpd (snd_l l) s a b) = a"
    using put_get
    by(auto simp add: snd_l_def split:prod.splits)
next
  fix s
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  assume  Hb : "b \<in> snd_l_S S s"
  thus "b <[ LUpd (snd_l l) s (LOut (snd_l l) s b) b"
    using get_put_weak
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
next
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  show "LUpd (snd_l l) s a b \<in> snd_l_S S s"
    using put_S
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
qed

lemma (in snd_l_valid_weak) ax :
  shows "lifting_valid_weak (snd_l l) (snd_l_S S)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in snd_l_valid_weak) ax_g :
  assumes H : "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_weak (snd_l l) (snd_l_S S)"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_weak_axioms
    by auto
qed


locale snd_l_valid_ext = lifting_valid_ext

sublocale snd_l_valid_ext \<subseteq> out : lifting_valid_ext "snd_l l" "snd_l_S S"
proof
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  (*assume  Hb : "b \<in> snd_l_S S s"*)
  show "b <[ LUpd (snd_l l) s a b"
    using get_put
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
qed

lemma (in snd_l_valid_ext) ax :
  shows "lifting_valid_ext (snd_l l)"
  using out.lifting_valid_ext_axioms
  by auto

locale snd_l_valid_base_ext = lifting_valid_base_ext
sublocale snd_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "snd_l l" "snd_l_S S"
proof
  fix s
  show "LBase (snd_l l) s = \<bottom>" using base
    by(auto simp add: snd_l_def prod_bot)
qed

lemma (in snd_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (snd_l l)"
  using out.lifting_valid_base_ext_axioms
  by auto

locale snd_l_valid_ok_ext = lifting_valid_ok_ext
sublocale snd_l_valid_ok_ext \<subseteq> out : lifting_valid_ok_ext "snd_l l" "snd_l_S S"
proof
  fix s

  show "ok_S \<subseteq> snd_l_S S s" using ok_S_valid
    by(auto simp add: prod_ok_S snd_l_S_def)
next
  fix s a
  fix b :: "('d * 'c)"
  assume B: "b \<in> ok_S" 
  then show "LUpd (snd_l l) s a b \<in> ok_S" using ok_S_put
    by(auto simp add: prod_ok_S snd_l_S_def snd_l_def)
qed

lemma (in snd_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (snd_l l) (snd_l_S S)"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in snd_l_valid_ok_ext) ax_g :
  assumes H: "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_ok_ext (snd_l l) (snd_l_S S)"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
  using out.lifting_valid_ok_ext_axioms
  by auto
qed


locale snd_l_valid_pres_ext = lifting_valid_pres_ext
sublocale snd_l_valid_pres_ext \<subseteq> out : lifting_valid_pres_ext "snd_l l" "snd_l_S S"
proof
  fix v supr :: "('d * 'c)"
  fix V f s

  assume HV : "v \<in> V"
  assume HS : "V \<subseteq> snd_l_S S s"
  assume Hsupr : "is_sup V supr"
  assume Hsupr_S : "supr \<in> snd_l_S S s"
  show "is_sup (LMap (snd_l l) f s ` V) (LMap (snd_l l) f s supr)"
  proof(rule is_supI)

    fix x

    assume Xin : "x \<in> LMap (snd_l l) f s ` V"

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    obtain xi xi1 xi2 where Xi : "xi = (xi1, xi2)" "xi \<in> V" "LMap (snd_l l) f s xi = x"
      using Xin
      by auto

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

    have "xi <[ supr" using is_supD1[OF Hsupr Xi(2)] by simp

    hence "xi1 <[ supr1" "xi2 <[ supr2"
      using Xi Supr
      by(auto simp add: prod_pleq split: prod.splits)

    have "x1 = xi1" using Xi X
      by(auto simp add: snd_l_def)

    have "x2 = LMap l f s xi2"
      using Xi X
      by(auto simp add: snd_l_def)

    have "LMap (snd_l l) f s supr = (supr1, LMap l f s supr2)"
      using Supr
      by(auto simp add: snd_l_def)

    have Xi1_in : "xi2 \<in> snd ` V"
      using imageI[OF `xi \<in> V`, of snd] Xi
      by(auto)

    have Fst_V_sub : "snd ` V \<subseteq> S s"
      using HS
      by(auto simp add: snd_l_S_def)

    have "supr2 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: snd_l_S_def)

    have Supr1_sup : "is_sup (snd ` V) supr2"
    proof(rule is_supI)
      fix w2
      assume "w2 \<in> snd ` V"

      then obtain w1 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w2 <[ supr2" using Supr by(auto simp add: prod_pleq)
    next

      fix z2

      assume Hub : "is_ub (snd ` V) z2"

      have "is_ub V (supr1, z2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w2 \<in> (snd ` V)"
          using imageI[OF `w \<in> V`, of snd] W by auto

        hence "w2 <[ z2" using is_ubE[OF Hub] by auto

        have "w1 <[ supr1" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (supr1, z2)" using W `w2 <[ z2`
          by(auto simp add: prod_pleq)
      qed

      show "supr2 <[ z2"
        using is_supD2[OF Hsupr `is_ub V (supr1, z2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    have Supr1_map : "is_sup (LMap l f s ` snd ` V) (LMap l f s supr2)"
      using pres using pres[OF Xi1_in Fst_V_sub Supr1_sup `supr2 \<in> S s` , of f]
      by simp

    have X1_in : "x2 \<in> LMap l f s ` snd ` V"
      using X Xi imageI[OF `xi \<in> V`, of snd]
      by(auto simp add: snd_l_def)

    have "x2 <[ LMap l f s supr2"
      using is_supD1[OF Supr1_map X1_in]
      by simp

    have "x1 <[ supr1" using `x1 = xi1` `xi1 <[ supr1` by simp

    then show "x <[ LMap (snd_l l) f s supr"
      using X Supr `x2 <[ LMap l f s supr2`
      by(auto simp add: snd_l_def prod_pleq)
  next
    fix x

    assume Xub : "is_ub (LMap (snd_l l) f s ` V) x"

    obtain supr1 supr2 where Supr : "supr = (supr1, supr2)" by(cases supr; auto)

  (* TODO: copy-pasted from first case *)
    have "LMap (snd_l l) f s supr = (supr1, LMap l f s supr2)"
      using Supr
      by(auto simp add: snd_l_def)

    have Snd_V_sub : "snd ` V \<subseteq> S s"
      using HS
      by(auto simp add: snd_l_S_def)

    have "supr2 \<in> S s"
      using Hsupr_S Supr
      by(auto simp add: snd_l_S_def)

    have Supr2_sup : "is_sup (snd ` V) supr2"
    proof(rule is_supI)
      fix w2
      assume "w2 \<in> snd ` V"

      then obtain w1 where "(w1, w2) \<in> V"
        by auto

      hence "(w1, w2) <[ supr" using is_supD1[OF Hsupr, of "(w1, w2)"] by auto

      thus "w2 <[ supr2" using Supr by(auto simp add: prod_pleq)
    next

      fix z2

      assume Hub : "is_ub (snd ` V) z2"

      have "is_ub V (supr1, z2)"
      proof(rule is_ubI)
        fix w
        assume "w \<in> V"

        obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

        have "w2 \<in> (snd ` V)"
          using imageI[OF `w \<in> V`, of snd] W by auto

        hence "w2 <[ z2" using is_ubE[OF Hub] by auto

        have "w1 <[ supr1" using is_supD1[OF Hsupr `w \<in> V`] Supr W
          by(auto simp add: prod_pleq)

        then show "w <[ (supr1, z2)" using W `w2 <[ z2`
          by(auto simp add: prod_pleq)
      qed

      show "supr2 <[ z2"
        using is_supD2[OF Hsupr `is_ub V (supr1, z2)`] Supr
        by(auto simp add: prod_pleq)
    qed

    obtain v1 v2 where V : "v = (v1, v2)" "v2 \<in> snd ` V"
      using imageI[OF HV, of snd]
      by(cases v; auto)

    have Supr2_map : "is_sup (LMap l f s ` snd ` V) (LMap l f s supr2)"
      using pres[OF V(2) Snd_V_sub Supr2_sup `supr2 \<in> S s` ] 
      by simp

    obtain x1 x2 where X: "x = (x1, x2)" by(cases x; auto)

    have X2_ub : "is_ub (LMap l f s ` snd ` V) x2"
    proof
      fix w2

      assume W2: "w2 \<in> LMap l f s ` snd ` V"

      then obtain wi wi1 wi2  where Wi : "wi \<in> V" "LMap l f s wi2 = w2" "wi = (wi1, wi2)"
        by(auto)

      have Wi_in : "LMap (snd_l l) f s wi \<in> LMap (snd_l l) f s ` V"
        using imageI[OF Wi(1), of "LMap (snd_l l) f s"] by simp

      have "LMap (snd_l l) f s wi <[ x"
        using is_ubE[OF Xub Wi_in]
        by simp

      then show "w2 <[ x2"
        using W2 Wi X
        by(auto simp add: prod_pleq snd_l_def)
    qed  

    have "LMap l f s supr2 <[ x2"
      using is_supD2[OF Supr2_map X2_ub]
      by simp

    have "is_ub V (x1, supr2)"
    proof(rule is_ubI)
      fix w

      assume Win : "w \<in> V"

      obtain w1 w2 where W: "w = (w1, w2)" by(cases w; auto)

      have W2_in : "w2 \<in> snd ` V"
        using imageI[OF Win, of snd] W by simp

      have "w2 <[ supr2"
        using is_supD1[OF Supr2_sup W2_in] by simp

      have "LMap (snd_l l) f s w <[ x"
        using is_ubE[OF Xub imageI[OF Win]] by simp

      hence "w1 <[ x1" using W X
        by(auto simp add: snd_l_def prod_pleq)

      show "w <[ (x1, supr2)"
        using `w2 <[ supr2` `w1 <[ x1` W
        by(auto simp add: prod_pleq)
    qed

    have "supr1 <[ x1"
      using is_supD2[OF Hsupr `is_ub V (x1, supr2)`] Supr
      by(auto simp add: prod_pleq)


    show "LMap (snd_l l) f s supr <[ x"
      using `LMap l f s supr2 <[ x2` `supr1 <[ x1` X Supr
      by(auto simp add: snd_l_def prod_pleq)
  qed
qed

lemma (in snd_l_valid_pres_ext) ax :
  shows "lifting_valid_pres_ext (snd_l l) (snd_l_S S)"
  using out.lifting_valid_pres_ext_axioms
  by auto

lemma (in snd_l_valid_pres_ext) ax_g :
  assumes H : "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_pres_ext (snd_l l) S'"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_pres_ext_axioms
  by auto
qed


locale snd_l_valid_base_pres_ext = snd_l_valid_pres_ext + snd_l_valid_base_ext + lifting_valid_base_pres_ext
sublocale snd_l_valid_base_pres_ext \<subseteq> out : lifting_valid_base_pres_ext "snd_l l" "snd_l_S S"
proof
  fix s
  show "\<bottom> \<notin> snd_l_S S s"
    using bot_bad[of s]
    by(auto simp add: snd_l_S_def prod_bot)
qed

lemma (in snd_l_valid_base_pres_ext) ax :
  shows "lifting_valid_base_pres_ext (snd_l l) (snd_l_S S)"
  using out.lifting_valid_base_pres_ext_axioms by auto

lemma (in snd_l_valid_base_pres_ext) ax_g :
  assumes H : "\<And> x . S' x = snd_l_S S x"
  shows "lifting_valid_base_pres_ext (snd_l l) S'"
proof-
  have "S' = snd_l_S S"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_base_pres_ext_axioms by auto
qed


(*
 * merge 
 *)


definition merge_l ::
  "('x, 'a1, 'b) lifting \<Rightarrow>
   ('x, 'a2, 'b) lifting \<Rightarrow>
   ('x, 'a1 * 'a2, 'b) lifting" where
"merge_l t1 t2 =
    LMake
      (\<lambda> s a b . 
        (case a of (a1, a2) \<Rightarrow>
          LUpd t1 s a1 (LUpd t2 s a2 b )))
      (\<lambda> s b . (LOut t1 s b, LOut t2 s b))
      (\<lambda> s . LBase t1 s)"

locale merge_l_valid_weak' = 
  fixes l1 :: "('x, 'a1, 'b) lifting" 
  fixes l2 :: "('x, 'a2, 'b) lifting"

locale merge_l_valid_weak =
  merge_l_valid_weak' +
  l_ortho +
  in1 : lifting_valid_weak l1 S1 +
  in2 : lifting_valid_weak l2 S2

sublocale merge_l_valid_weak \<subseteq> out : lifting_valid_weak "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s
  fix a :: "'b * 'd"
  fix b :: "'c"
  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have "LUpd l2 s a2 (LUpd l1 s a1 b) \<in> S1 s"
    unfolding sym[OF compat]
    using in1.put_S
    by auto

  then show "LUpd (merge_l l1 l2) s a b \<in> S1 s \<inter> S2 s" using A in2.put_S
    by(simp add: merge_l_def compat)

next
  fix s b
  fix a :: "'b * 'd"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have "LOut l2 s (LUpd l1 s a1 (LUpd l2 s a2 b)) = a2"
    unfolding compat
    using in2.put_get
    by auto

  then show "LOut (merge_l l1 l2) s (LUpd (merge_l l1 l2) s a b) = a"
    using A in1.put_get 
    by(auto simp add: merge_l_def)

next
  fix s 
  fix b :: "'c"
  assume "b \<in> S1 s \<inter> S2 s"

  then have B1 : "b \<in> S1 s" and B2 : "b \<in> S2 s"
    by auto

  have Leq1 : "b <[ (LUpd l2 s (LOut l2 s b) b)"
    using in2.get_put_weak[OF B2]
    by auto

  have Eq : "LOut l1 s (LUpd l2 s (LOut l2 s b) b) = LOut l1 s b"
    using put2_get1
    by auto

  have Upd_in : "LUpd l2 s (LOut l2 s b) b \<in> S1 s"
    using put2_S1[OF B1]
    by auto

  have "b <[ LUpd l1 s (LOut l1 s b) b"
    using in1.get_put_weak[OF B1] by auto

  show "b <[ LUpd (merge_l l1 l2) s (LOut (merge_l l1 l2) s b) b"
    using leq_trans[OF Leq1 in1.get_put_weak[OF Upd_in]]
    by(auto simp add: merge_l_def Eq)
qed

lemma (in merge_l_valid_weak) ax :
  shows "lifting_valid_weak (merge_l l1 l2) (\<lambda> x . S1 x \<inter> S2 x)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in merge_l_valid_weak) ax_g :
  assumes H : "\<And> x . S' x = (\<lambda> x . S1 x \<inter> S2 x) x"
  shows "lifting_valid_weak (merge_l l1 l2) S'"
proof-
  have "S' = (\<lambda> x . S1 x \<inter> S2 x)"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_weak_axioms
    by auto
qed

locale merge_l_valid_ext = merge_l_valid_weak' +
  in1 : lifting_valid_ext l1 +
  in2 : lifting_valid_ext l2 

sublocale merge_l_valid_ext \<subseteq> out : lifting_valid_ext "merge_l l1 l2"
proof

  fix s
  fix a :: "'b * 'd"
  fix b :: "'c"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have Leq1 : "b <[ LUpd l2 s a2 b"
    using in2.get_put by auto

  have Leq2 : "LUpd l2 s a2 b <[ LUpd l1 s a1 (LUpd l2 s a2 b)"
    using in1.get_put by auto

  show "b <[ LUpd (merge_l l1 l2) s a b" 
    using A leq_trans[OF Leq1 Leq2]
    by(auto simp add: merge_l_def)
qed

lemma (in merge_l_valid_ext) ax :
  shows "lifting_valid_ext (merge_l l1 l2)"
  using out.lifting_valid_ext_axioms by auto

locale merge_l_valid_base_ext =
  l_ortho_base +
  in1 : lifting_valid_base_ext l1 S1 +
  in2 : lifting_valid_base_ext l2 S2

sublocale merge_l_valid_base_ext \<subseteq> out : lifting_valid_base_ext "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s :: "'a"

  show "LBase (merge_l l1 l2) s = \<bottom>"
    using in1.base
    by(auto simp add: merge_l_def)
qed

lemma (in merge_l_valid_base_ext) ax :
  shows "lifting_valid_base_ext (merge_l l1 l2)"
  using out.lifting_valid_base_ext_axioms
  by auto

locale merge_l_valid_ok_ext = l_ortho_ok +
  in1 : lifting_valid_ok_ext l1 S1 +
  in2 : lifting_valid_ok_ext l2 S2

sublocale merge_l_valid_ok_ext \<subseteq> out : lifting_valid_ok_ext "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s

  show "ok_S \<subseteq> S1 s \<inter> S2 s"
    using in1.ok_S_valid in2.ok_S_valid by auto
next
  fix s 
  fix a :: "'b * 'd"
  fix b :: "'c"

  assume B_ok : "b \<in> ok_S"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  show "LUpd (merge_l l1 l2) s a b \<in> ok_S"
    using A in1.ok_S_put in2.ok_S_put B_ok
    by(auto simp add: merge_l_def)
qed

lemma (in merge_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (merge_l l1 l2) (\<lambda> x . S1 x \<inter> S2 x)"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in merge_l_valid_ok_ext) ax_g :
  assumes H : "\<And> x . S' x = (\<lambda> x . S1 x \<inter> S2 x) x"
  shows "lifting_valid_ok_ext (merge_l l1 l2) S'"
proof-
  have "S' = (\<lambda> x . S1 x \<inter> S2 x)"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_ok_ext_axioms
    by auto
qed


(* TODO: make sure we don't actually need this. *)
(*
locale merge_l_valid_pres_ext = merge_l_valid_weak +
  l_ortho_pres +
  in1 : lifting_valid_pres_ext l1 S1 +
  in2 : lifting_valid_pres_ext l2 S2


sublocale merge_l_valid_pres_ext \<subseteq> out: lifting_valid_pres_ext "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix v supr :: "'c"
  fix V
  fix f :: "'a \<Rightarrow> 'b * 'd \<Rightarrow> 'b * 'd"
  fix s :: 'a
  assume Vin : "v \<in> V"
  assume Vsub : "V \<subseteq> S1 s \<inter> S2 s"
  then have Vsub1 : "V \<subseteq> S1 s" and Vsub2 : "V \<subseteq> S2 s"
    by auto

  assume Supr : "is_sup V supr" 
  assume Supr_in : "supr \<in> S1 s \<inter> S2 s"

  then have Supr_in1 : "supr \<in> S1 s" and Supr_in2 : "supr \<in> S2 s"
    by auto
(*
  obtain f1 f2 where F: "f = (f1, f2)"
    by(cases f; auto)
*)
(*
  show "is_sup (LMap (merge_l l1 l2) f s ` V)
        (LMap (merge_l l1 l2) f s supr)"
    apply(simp add: merge_l_def)
*)

  obtain x1 x2 where X12 : "f s (LOut l1 s supr, LOut l2 s supr) = (x1, x2)"
    by(fastforce)

  have Supr' : "is_sup {LUpd l1 s x1 supr, LUpd l2 s x2 supr} (LUpd l1 s x1 (LUpd l2 s x2 supr))"
    using compat_pres_sup
    by auto


  show "is_sup (LMap (merge_l l1 l2) f s ` V) (LMap (merge_l l1 l2) f s supr)"
(*
    using compat_pres_pair[OF Vin Vsub1 Vsub2 Supr Supr_in, of f]
    by(auto simp add: merge_l_def)
*)
  proof(rule is_supI)
    fix x

    assume X: "x \<in> LMap (merge_l l1 l2) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (merge_l l1 l2) f s xo = x"
      by auto

    show "x <[ LMap (merge_l l1 l2) f s supr"
      using Xo
      apply(auto simp add: merge_l_def split: prod.splits)


    qed
*)

locale merge_l_valid_pairwise_ext =
  l_ortho +
  in1 : lifting_valid_pairwise_ext S1 +
  in2 : lifting_valid_pairwise_ext S2

sublocale merge_l_valid_pairwise_ext \<subseteq> out : lifting_valid_pairwise_ext "(\<lambda> x . S1 x \<inter> S2 x)"
proof
  show "\<And>x1 x2 x3 s s12 s23 s13 s123.
       x1 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       x2 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       x3 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x1, x2} s12 \<Longrightarrow>
       s12 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x2, x3} s23 \<Longrightarrow>
       s23 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x1, x3} s13 \<Longrightarrow>
       s13 \<in> S1 s \<inter> S2 s \<Longrightarrow>
       is_sup {x1, x2, x3} s123 \<Longrightarrow> s123 \<in> S1 s \<inter> S2 s"
    using in1.pairwise_S in2.pairwise_S
    by blast
qed

lemma (in merge_l_valid_pairwise_ext) ax :
  shows "lifting_valid_pairwise_ext (\<lambda> x . S1 x \<inter> S2 x)"
  using out.lifting_valid_pairwise_ext_axioms
  by auto

lemma (in merge_l_valid_pairwise_ext) ax_g :
  assumes H: "\<And> x . S' x = (\<lambda> x . S1 x \<inter> S2 x) x"
  shows "lifting_valid_pairwise_ext S'"
proof-
  have "S' = (\<lambda> x . S1 x \<inter> S2 x)"
    using assms by auto
  then show ?thesis
    using out.lifting_valid_pairwise_ext_axioms
    by auto
qed


(* Next we declare some instances for ortho.
 * The most useful ones are the ones for products
 * (fst/fst, snd/snd, fst/snd, and merges *)

locale option_l_ortho =
  l_ortho

(* YOU ARE HERE *)
(* TODO: slice up ortho explicitly into a core and extensions instead of a series of growing structures.
 * then, like before, prove extensions from extensions (i.e. minimally)
 * in order to lower the burden of copying lots of code/proofs or worrying about things
 * getting propagated correctly
*)
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

lemma sup_singleton :
  "is_sup {x} x"
  by(auto simp add: is_least_def is_ub_def is_sup_def leq_refl)

locale option_l_ortho_base = option_l_ortho + l_ortho_base'

sublocale option_l_ortho_base \<subseteq> out : l_ortho_base "option_l l1" "option_l_S S1" "option_l l2" "option_l_S S2"
proof
  fix s

  show "LBase (option_l l1) s = \<bottom>"
    by(auto simp add: option_l_def option_bot)
next

  fix s
  show "LBase (option_l l2) s = \<bottom>"
    by(auto simp add: option_l_def option_bot)
qed
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



locale option_l_ortho_ok =
  option_l_ortho + l_ortho_ok

sublocale option_l_ortho_ok \<subseteq> out : l_ortho_ok "option_l l1" "option_l_S S1" "option_l l2" "option_l_S S2"
proof
qed

(* Prio - let's defer this until later as we may not need it.
 * my guess is it's true, but annoying. *)

(*
locale prio_l_ortho =
  l_ortho 
*)

(* next, products:
- ortho between fst and fst, if inner liftings ortho
- snd and snd, ditto
- fst and snd, unconditionally
*)


locale fst_l_ortho = l_ortho

sublocale fst_l_ortho \<subseteq> out : l_ortho "fst_l l1" "fst_l_S S1" "fst_l l2" "fst_l_S S2"
proof
  fix s
  show "LBase (fst_l l1) s = LBase (fst_l l2) s"
    using eq_base
    by(auto simp add: fst_l_def)
next

  fix b :: "'c * 'e"
  fix s
  fix a1 :: 'b
  fix a2 :: 'd

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)
  have Compat1 : "LUpd l1 s a1 (LUpd l2 s a2 b1) = LUpd l2 s a2 (LUpd l1 s a1 b1)"
    using compat[of s a1 a2 b1]
    by(auto)

  then show "LUpd (fst_l l1) s a1 (LUpd (fst_l l2) s a2 b) =
       LUpd (fst_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    using B
    by(auto simp add: fst_l_def)
next

  fix b :: "('c * 'e)"
  fix a1 
  fix s

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l2 s (LUpd l1 s a1 b1) = LOut l2 s b1"
    using put1_get2
    by auto

  then show "LOut (fst_l l2) s (LUpd (fst_l l1) s a1 b) = LOut (fst_l l2) s b"
    using B
    by (auto simp add: fst_l_def)
next
  fix b :: "('c * 'e)"
  fix s a2

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l1 s (LUpd l2 s a2 b1) = LOut l1 s b1"
    using put2_get1
    by auto

  then show "LOut (fst_l l1) s
        (LUpd (fst_l l2) s a2 b) =
       LOut (fst_l l1) s b"
    using B
    by(auto simp add: fst_l_def)
next
  fix b :: "'c * 'e"
  fix s a1

  assume B_in : "b \<in> fst_l_S S2 s"

  then obtain b1 b2 where B : "b = (b1, b2)" "b1 \<in> S2 s"
    by(auto simp add: fst_l_S_def)

  have Compat1 : "LUpd l1 s a1 b1 \<in> S2 s"
    using put1_S2[OF B(2)] by auto

  then show "LUpd (fst_l l1) s a1 b \<in> fst_l_S S2 s"
    using B
    by(auto simp add: fst_l_def fst_l_S_def)
next
  fix b :: "'c * 'e"
  fix s a2

  assume B_in : "b \<in> fst_l_S S1 s"
  then obtain b1 b2 where B : "b = (b1, b2)" "b1 \<in> S1 s"
    by(auto simp add: fst_l_S_def)

  have Compat2 : "LUpd l2 s a2 b1 \<in> S1 s"
    using put2_S1[OF B(2)]
    by auto
  
  then show "LUpd (fst_l l2) s a2 b \<in> fst_l_S S1 s"
    using B
    by(auto simp add: fst_l_def fst_l_S_def)
qed

locale fst_l_ortho_base = fst_l_ortho + l_ortho_base

sublocale fst_l_ortho_base \<subseteq> out : l_ortho_base "fst_l l1" "fst_l_S S1" "fst_l l2" "fst_l_S S2"
proof
  fix s
  show "LBase (fst_l l1) s = \<bottom>"
    using compat_base1
    by(auto simp add: fst_l_def prod_bot)
  fix s
  show "LBase (fst_l l2) s = \<bottom>"
    using compat_base2
    by(auto simp add: fst_l_def prod_bot)
qed

locale fst_l_ortho_pres = fst_l_ortho + l_ortho_pres

sublocale fst_l_ortho_pres \<subseteq> l_ortho_pres "fst_l l1" "fst_l_S S1" "fst_l l2" "fst_l_S S2"
proof
 fix a1 a2 s 
  fix x :: "('c * 'e)"

  obtain x1 x2 where X : "x = (x1, x2)"
    by(cases x; auto)

  have Sup : 
    "is_sup {LUpd (l1) s a1 x1, LUpd (l2) s a2 x1}
        (LUpd (l1) s a1 (LUpd (l2) s a2 x1))"
    using compat_pres_sup
    by auto

  have Conc' :
    "is_sup ((\<lambda>w. (w, x2)) ` {LUpd l1 s a1 x1, LUpd l2 s a2 x1}) (LUpd l1 s a1 (LUpd l2 s a2 x1), x2)"
    using is_sup_fst[OF _ Sup]
    by auto

  then show "is_sup {LUpd (fst_l l1) s a1 x, LUpd (fst_l l2) s a2 x}
        (LUpd (fst_l l1) s a1 (LUpd (fst_l l2) s a2 x))"
    using X
    by(auto simp add: fst_l_def)

(* YOU ARE HERE
we need to figure out whether we really fixed this problem.
*)
qed

(* snd (copy-paste-change from fst) *)
locale snd_l_ortho = l_ortho

sublocale snd_l_ortho \<subseteq> out : l_ortho "snd_l l1" "snd_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s
  show "LBase (snd_l l1) s = LBase (snd_l l2) s"
    using eq_base
    by(auto simp add: snd_l_def)
next

  fix b :: "('e * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'd

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LUpd l1 s a1 (LUpd l2 s a2 b2) = LUpd l2 s a2 (LUpd l1 s a1 b2)"
    using compat[of s a1 a2 b2]
    by(auto)

  then show "LUpd (snd_l l1) s a1 (LUpd (snd_l l2) s a2 b) =
       LUpd (snd_l l2) s a2 (LUpd (snd_l l1) s a1 b)"
    using B
    by(auto simp add: snd_l_def)
next

  fix b :: "('e * 'c)"
  fix a1 
  fix s

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l2 s (LUpd l1 s a1 b2) = LOut l2 s b2"
    using put1_get2
    by auto

  then show "LOut (snd_l l2) s (LUpd (snd_l l1) s a1 b) = LOut (snd_l l2) s b"
    using B
    by (auto simp add: snd_l_def)
next
  fix b :: "('e * 'c)"
  fix s a2

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have Compat1 : "LOut l1 s (LUpd l2 s a2 b2) = LOut l1 s b2"
    using put2_get1
    by auto

  then show "LOut (snd_l l1) s
        (LUpd (snd_l l2) s a2 b) =
       LOut (snd_l l1) s b"
    using B
    by(auto simp add: snd_l_def)
next
  fix b :: "'e * 'c"
  fix s a1

  assume B_in : "b \<in> snd_l_S S2 s"

  then obtain b1 b2 where B : "b = (b1, b2)" "b2 \<in> S2 s"
    by(auto simp add: snd_l_S_def)

  have Compat1 : "LUpd l1 s a1 b2 \<in> S2 s"
    using put1_S2[OF B(2)] by auto

  then show "LUpd (snd_l l1) s a1 b \<in> snd_l_S S2 s"
    using B
    by(auto simp add: snd_l_def snd_l_S_def)
next
  fix b :: "'e * 'c"
  fix s a2

  assume B_in : "b \<in> snd_l_S S1 s"
  then obtain b1 b2 where B : "b = (b1, b2)" "b2 \<in> S1 s"
    by(auto simp add: snd_l_S_def)

  have Compat2 : "LUpd l2 s a2 b2 \<in> S1 s"
    using put2_S1[OF B(2)]
    by auto
  
  then show "LUpd (snd_l l2) s a2 b \<in> snd_l_S S1 s"
    using B
    by(auto simp add: snd_l_def snd_l_S_def)
qed

locale snd_l_ortho_base = snd_l_ortho + l_ortho_base

sublocale snd_l_ortho_base \<subseteq> out : l_ortho_base "snd_l l1" "snd_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s
  show "LBase (snd_l l1) s = \<bottom>"
    using compat_base1
    by(auto simp add: snd_l_def prod_bot)
next
  fix s
  show "LBase (snd_l l2) s = \<bottom>"
    using compat_base2
    by(auto simp add: snd_l_def prod_bot)
qed

locale snd_l_ortho_pres = snd_l_ortho + l_ortho_pres

sublocale snd_l_ortho_pres \<subseteq> l_ortho_pres "snd_l l1" "snd_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix a1 a2 s
  fix x :: "'e * 'c"
  obtain x1 x2 where X : "x = (x1, x2)"
    by(cases x; auto)

  have Sup : 
    "is_sup {LUpd (l1) s a1 x2, LUpd (l2) s a2 x2}
        (LUpd (l1) s a1 (LUpd (l2) s a2 x2))"
    using compat_pres_sup
    by auto

  have Conc' :
    "is_sup ((\<lambda>w. (x1, w)) ` {LUpd l1 s a1 x2, LUpd l2 s a2 x2}) (x1, LUpd l1 s a1 (LUpd l2 s a2 x2))"
    using is_sup_snd[OF _ Sup]
    by auto

  then show "is_sup {LUpd (snd_l l1) s a1 x, LUpd (snd_l l2) s a2 x}
        (LUpd (snd_l l1) s a1 (LUpd (snd_l l2) s a2 x))"
    using X
    by(auto simp add: snd_l_def)
qed

locale fst_l_snd_l_ortho' =
  fixes l1 :: "('a, 'b1, 'c1 :: Pordb) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c1 set"
  fixes l2 :: "('a, 'b2, 'c2 :: Pordb) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c2 set"

locale fst_l_snd_l_ortho = fst_l_snd_l_ortho' +
  in1 : lifting_valid_base l1 S1 +
  in2 : lifting_valid_base l2 S2

sublocale fst_l_snd_l_ortho \<subseteq> out : l_ortho "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s
  show "LBase (fst_l l1) s = LBase (snd_l l2) s"
    using in1.base in2.base
    by(auto simp add: fst_l_def snd_l_def)
next
  fix b :: "'c * 'e"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'd

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b) = LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    by(auto simp add: fst_l_def snd_l_def)

next

  fix b :: "'c * 'e"
  fix s :: 'a
  fix a1

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LOut (snd_l l2) s (LUpd (fst_l l1) s a1 b) = LOut (snd_l l2) s b"
    by(auto simp add: fst_l_def snd_l_def)
next

  fix b :: "'c * 'e"
  fix s :: 'a
  fix a2 :: 'd


  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LOut (fst_l l1) s (LUpd (snd_l l2) s a2 b) = LOut (fst_l l1) s b"
    by(cases b; auto simp add: fst_l_def snd_l_def)


next
  fix b :: "'c * 'e"
  fix s :: 'a
  fix a1 :: 'b

  assume Bin : "b \<in> snd_l_S S2 s"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show " LUpd (fst_l l1) s a1 b \<in> snd_l_S S2 s" using Bin
    by(auto simp add: fst_l_def snd_l_S_def)
next
  fix b :: "'c * 'e"
  fix s :: 'a
  fix a2 :: 'd

  assume Bin: "b \<in> fst_l_S S1 s"
  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LUpd (snd_l l2) s a2 b \<in> fst_l_S S1 s" using Bin
    by(auto simp add: snd_l_def fst_l_S_def)
qed
(*
(* lifting_valid_weak_ok *)
locale fst_l_snd_l_ortho_ok =
  fst_l_snd_l_ortho + 
  in1 : lifting_valid_weak_ok l1 S1 +
  in2 : lifting_valid_weak_ok l2 S2

sublocale fst_l_snd_l_ortho_ok \<subseteq> out : l_ortho_ok "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

  assume Bok : "b \<in> ok_S"

  assume Sup : "is_sup {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr"
  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain supr1 supr2 where Sup1_2 : "supr = (supr1, supr2)"
    by(cases supr; auto)

  have Sup' : "is_sup {LUpd (fst_l l1) s a1 b,
                LUpd (snd_l l2) s a2 b}
        ((LUpd l1 s a1 b1), (LUpd l2 s a2 b2))"
  proof(rule is_supI)
    fix x

    assume X: "x \<in> {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b}"

    then consider (X1) "x = LUpd (fst_l l1) s a1 b" |
                  (X2) "x = LUpd (snd_l l2) s a2 b"
      by auto

    then show "x <[ (LUpd l1 s a1 b1, LUpd l2 s a2 b2)"
    proof cases
      case X1
      then show ?thesis using B leq_refl in2.get_put
        by(auto simp add: fst_l_def prod_pleq)
    next
      case X2
      then show ?thesis using B leq_refl in1.get_put
        by(auto simp add: snd_l_def prod_pleq)
    qed
  next

    fix x'
    assume Ub : "is_ub {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b} x'"

    obtain x'1 x'2 where X': "x' = (x'1, x'2)"
      by(cases x'; auto)

    have Up1 : "LUpd l1 s a1 b1 <[ x'1" and Up2 : "LUpd l2 s a2 b2 <[ x'2"
      using X' B is_ubE[OF Ub]
      by(auto simp add: fst_l_def snd_l_def prod_pleq)

    then show "(LUpd l1 s a1 b1, LUpd l2 s a2 b2) <[ x'"
      using X'
      by(auto simp add: prod_pleq)
  qed

  have Sup_eq : "supr = ((LUpd l1 s a1 b1), (LUpd l2 s a2 b2))"
    using is_sup_unique[OF Sup Sup']
    by auto

  then show "supr \<in> ok_S"
    using Bok B in1.ok_S_put in2.ok_S_put
    by(auto simp add: prod_ok_S)
qed
*)
locale fst_l_snd_l_ortho_base =
  fst_l_snd_l_ortho + 
  in1 : lifting_valid_weak_base l1 S1 +
  in2 : lifting_valid_weak_base l2 S2


sublocale fst_l_snd_l_ortho_base \<subseteq> out : l_ortho_base "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s
  show "LBase (fst_l l1) s = \<bottom>"
    using in1.base
    by(auto simp add: fst_l_def prod_bot)
next
  fix s
  show "LBase (snd_l l2) s = \<bottom>"
    using in2.base
    by(auto simp add: snd_l_def prod_bot)
qed

  

(* TODO: this was originally lifting_valid_weak_pres, but i think we actually need strength
 * to make this work *)
locale fst_l_snd_l_ortho_pres =
  fst_l_snd_l_ortho +
  in1 : lifting_valid_pres l1 S1 +
  in2 : lifting_valid_pres l2 S2

sublocale fst_l_snd_l_ortho_pres \<subseteq> out : l_ortho_pres "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix a1 a2 s
  fix x :: "('c * 'e)"

  obtain x1 x2 where X: "x = (x1, x2)"
    by(cases x; auto)

  have Leq1 : "x1 <[ LUpd l1 s a1 x1"
    using in1.get_put by auto

  have Leq2 : "x2 <[ LUpd l2 s a2 x2"
    using in2.get_put by auto

  show "is_sup {LUpd (fst_l l1) s a1 x, LUpd (snd_l l2) s a2 x} (LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 x))"
  proof(rule is_supI)
    fix w

    assume W: "w \<in> {LUpd (fst_l l1) s a1 x, LUpd (snd_l l2) s a2 x}"

    obtain w1 w2 where "w = (w1, w2)"
      by(cases w; auto)

    show "w <[ LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 x)"
      using W X Leq1 Leq2
      by(auto simp add: fst_l_def snd_l_def prod_pleq leq_refl)
  next
    fix x'
    assume Ub : "is_ub {LUpd (fst_l l1) s a1 x, LUpd (snd_l l2) s a2 x} x'"

    obtain x'1 x'2 where X': "x' = (x'1, x'2)"
      by(cases x'; auto)

    have Leq1 : "LUpd (fst_l l1) s a1 x <[ x'"
      using is_ubE[OF Ub]
      by auto

    have Leq2 : "LUpd (snd_l l2) s a2 x <[ x'"
      using is_ubE[OF Ub]
      by auto

    show "LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 x) <[ x'"
      using X' X Leq1 Leq2
      by(auto simp add: fst_l_def snd_l_def prod_pleq)
  qed
qed


locale merge_l_ortho' =
  fixes l1 :: "('a, 'b1, 'c :: {Mergeableb, Pordps}) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c1 set"
  fixes l2 :: "('a, 'b2, 'c) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c2 set"
  fixes l3 :: "('a, 'b3, 'c) lifting"
  fixes S3 :: "'a \<Rightarrow> 'c3 set"

locale merge_l_ortho = merge_l_ortho' +
  orth1_2 : l_ortho l1 S1 l2 S2 + 
  orth1_3 : l_ortho l1 S1 l3 S3 +
  orth2_3 : l_ortho l2 S2 l3 S3 
  (* + valid3 : lifting_valid_weak_pres l3 S3*)
(* TODO may need more validity assumptions. *)

sublocale merge_l_ortho \<subseteq> out : l_ortho "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x" l3 S3
proof
  fix s

  have Supr : "is_sup {LBase l2 s, LBase l2 s} (LBase l2 s)"
    using sup_singleton[of "LBase l2 s"]
    by auto

  have Supr' : "is_sup {LBase l2 s, LBase l2 s}
     [^ LBase l2 s, LBase l2 s ^]"
    using bsup_sup[OF Supr bsup_spec]
    by auto

  then have "[^ LBase l2 s, LBase l2 s ^] = LBase l2 s"
    using is_sup_unique[OF Supr Supr'] by auto

  then show "LBase (merge_l l1 l2) s = LBase l3 s"
    using orth1_3.eq_base[of s] orth2_3.eq_base[of s]
    by(auto simp add: merge_l_def)

next
  fix b :: 'c
  fix a1_2 :: "'b * 'd"
  fix a3 :: 'e
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LUpd (merge_l l1 l2) s a1_2 (LUpd l3 s a3 b) = LUpd l3 s a3 (LUpd (merge_l l1 l2) s a1_2 b)" using A1_2
    by(auto simp add: merge_l_def orth1_3.compat orth2_3.compat)

next
  fix b :: 'c
  fix a1_2 :: "'b * 'd"
  fix a3 :: 'e
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LOut l3 s (LUpd (merge_l l1 l2) s a1_2 b) = LOut l3 s b" using A1_2
    by(auto simp add: merge_l_def orth1_3.put1_get2 orth2_3.put1_get2)
next

  fix b :: 'c
  fix a1_2 :: "'b * 'd"
  fix a3 :: 'e
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LOut (merge_l l1 l2) s (LUpd l3 s a3 b) = LOut (merge_l l1 l2) s b" using A1_2
    by(auto simp add: merge_l_def orth1_3.put2_get1 orth2_3.put2_get1)
next

  fix b s
  fix a1_2 :: "'b * 'd"
  assume B: "b \<in> S3 s"

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  have Up2 : "(LUpd l2 s a2 b) \<in> S3 s"
    using orth2_3.put1_S2[OF B] by auto

  have Up1 : "(LUpd l1 s a1 (LUpd l2 s a2 b)) \<in> S3 s"
    using orth1_3.put1_S2[OF Up2]
    by auto

  then show "LUpd (merge_l l1 l2) s a1_2 b \<in> S3 s" using A1_2
    by(auto simp add: merge_l_def)
next

  fix b s
  fix a3 :: 'e

  assume B: "b \<in> S1 s \<inter> S2 s"

  then have B1 : "b \<in> S1 s" and B2 : "b \<in> S2 s"
    by auto

  have Conc1 : "LUpd l3 s a3 b \<in> S1 s"
    using orth1_3.put2_S1[OF B1] by auto

  have Conc2 : "LUpd l3 s a3 b \<in> S2 s"
    using orth2_3.put2_S1[OF B2] by auto

  show "LUpd l3 s a3 b \<in> S1 s \<inter> S2 s"
    using Conc1 Conc2
    by auto
qed

locale merge_l_ortho_base = merge_l_ortho +
  orth1_2 : l_ortho_base l1 S1 l2 S2 + 
  orth1_3 : l_ortho_base l1 S1 l3 S3 +
  orth2_3 : l_ortho_base l2 S2 l3 S3 

sublocale merge_l_ortho_base \<subseteq> l_ortho_base "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x" l3 S3
proof
  fix s

  show "LBase (merge_l l1 l2) s = \<bottom>"
    using orth1_2.compat_base1
    by(auto simp add: merge_l_def)
next

  fix s

  show "LBase l3 s = \<bottom>"
    using orth1_3.compat_base2
    by(auto)
qed

locale merge_l_ortho_pres = merge_l_ortho +
  orth1_2 : l_ortho_pres l1 S1 l2 S2 +
  orth1_3 : l_ortho_pres l1 S1 l3 S3 +
  orth2_3 : l_ortho_pres l2 S2 l3 S3 +
  (* see if we can avoid this presonly assumptions - i don't think we can though. *)
  in1 : lifting_valid_pres l1 S1 +
  in2 : lifting_valid_pres l2 S2 +
  in3 : lifting_valid_pres l3 S3

sublocale merge_l_ortho_pres \<subseteq> l_ortho_pres "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x" l3 S3
proof
  fix a1_2 :: "'b * 'd"
  fix a3 s 
  fix x :: 'c

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  have Merge_eq : "LUpd (merge_l l1 l2) s a1_2 (LUpd l3 s a3 x) = LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x))"
    using A1_2
    by(auto simp add: merge_l_def)

  have Sup23 : "is_sup {LUpd l2 s a2 x, LUpd l3 s a3 x} (LUpd l2 s a2 (LUpd l3 s a3 x))"
    using orth2_3.compat_pres_sup
    by auto

  have Sup123 : "is_sup {LUpd l1 s a1 (LUpd l3 s a3 x), LUpd l2 s a2 (LUpd l3 s a3 x)} (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using orth1_2.compat_pres_sup
    by auto

  have Sup13 : "is_sup {LUpd l1 s a1 x, LUpd l3 s a3 x} (LUpd l1 s a1 (LUpd l3 s a3 x))"
    using orth1_3.compat_pres_sup
    by auto

  have Eq_123 : "({LUpd l1 s a1 x, LUpd l3 s a3 x} \<union> {LUpd l2 s a2 x, LUpd l3 s a3 x}) = {LUpd l1 s a1 x, LUpd l2 s a2 x, LUpd l3 s a3 x}"
    by auto

  have Sup123' : "is_sup ({LUpd l1 s a1 x, LUpd l2 s a2 x, LUpd l3 s a3 x}) (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using sup_union1[OF Sup13 Sup23 Sup123]
    unfolding Eq_123
    by auto

  have Sup12 : "is_sup {LUpd l1 s a1 x, LUpd l2 s a2 x} (LUpd l1 s a1 (LUpd l2 s a2 x))"
    using orth1_2.compat_pres_sup
    by auto

  have Sup3 : "is_sup {LUpd l3 s a3 x} (LUpd l3 s a3 x)"
    using sup_singleton
    by auto

  have Eq_123' : "{LUpd l1 s a1 x, LUpd l2 s a2 x, LUpd l3 s a3 x} = {LUpd l1 s a1 x, LUpd l2 s a2 x} \<union> {LUpd l3 s a3 x}"
    by auto

  have Sup123'' : "is_sup ({LUpd l1 s a1 x, LUpd l2 s a2 x} \<union> {LUpd l3 s a3 x}) (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using Sup123' unfolding Eq_123'
    by auto

  have Conc' : "is_sup {(LUpd l1 s a1 (LUpd l2 s a2 x)), LUpd l3 s a3 x} (LUpd l1 s a1 (LUpd l2 s a2 (LUpd l3 s a3 x)))"
    using sup_union2[OF Sup12 Sup3 Sup123'']
    by auto

  have Merge_eq' : "LUpd (merge_l l1 l2) s a1_2 x = LUpd l1 s a1 (LUpd l2 s a2 x)"
    using A1_2
    by(auto simp add: merge_l_def)

  show "is_sup {LUpd (merge_l l1 l2) s a1_2 x, LUpd l3 s a3 x} (LUpd (merge_l l1 l2) s a1_2 (LUpd l3 s a3 x))"
    using Conc' unfolding Merge_eq Merge_eq'
    by simp
qed

end