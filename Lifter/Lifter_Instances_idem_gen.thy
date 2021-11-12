theory Lifter_Instances_idem imports Lifter_idem "../Mergeable/Mergeable_Facts"
begin

class Bogus =
  fixes bogus :: "'a"

instantiation nat :: Bogus begin
definition nat_bogus : "bogus = (0 :: nat)"
instance proof qed
end

instantiation bool :: Bogus begin
definition bool_bogus : "bogus = True"
instance proof qed
end

instantiation int :: Bogus begin
definition int_bogus : "bogus = (0 :: int)"
instance proof qed
end

instantiation unit :: Bogus begin
definition unit_bogus : "bogus = ()"
instance proof qed
end

instantiation prod :: (Bogus, Bogus) Bogus begin
definition prod_bogus : "bogus = (bogus, bogus)"
instance proof qed
end

instantiation sum :: (Bogus, _) Bogus begin
definition sum_bogus : "bogus = Inl bogus"
instance proof qed
end

instantiation option :: (Bogus) Bogus begin
definition option_bogus : "bogus = Some bogus"
instance proof qed
end

(* TODO: why not [bogus]? *)
instantiation list :: (_) Bogus begin
definition list_bogus : "bogus = []"
instance proof qed
end

instantiation md_triv :: (Bogus) Bogus begin
definition md_triv_bogus : "bogus = mdt bogus"
instance proof qed
end

instantiation md_prio :: (Bogus) Bogus begin
definition md_prio_bogus : "bogus = mdp 0 bogus"
instance proof qed
end

instantiation oalist :: (linorder, _) Bogus begin
definition oalist_bogus : "bogus = (empty :: (_, _) oalist)"
instance proof qed
end

instantiation String.literal :: Bogus begin
definition string_literal_bogus :
"bogus = STR ''''"
instance proof qed
end

(* TODO: add VSG versions of these, and hopefully
   figure out a way to infer. *)
(*
 * id
 *)
definition id_l ::
  "('x, 'a :: {Pord, Bogus}, 'a, ('x \<Rightarrow> 'a \<Rightarrow> 'a)) lifting" where
"id_l =
  LMake (\<lambda> s a a' . a) (\<lambda> s a . a) (\<lambda> s a . a) (\<lambda> s . bogus) (\<lambda> f x . f x)" 

interpretation id_l: lifting_valid_weak "id_l" "\<lambda> _ . UNIV"
proof
  show "\<And>s a b. LOut id_l s (LUpd_Idem id_l s a b) = a"
    by(auto simp add: id_l_def)
next
  show "\<And>s b. LOut id_l s (LPost id_l s b) = LOut id_l s b"
    by(auto simp add: id_l_def)
next
  show "\<And>s a b. LUpd_Idem id_l s a b \<in> UNIV"
    by auto
next
  show "\<And>s b. b \<in> UNIV \<Longrightarrow> LPost id_l s b \<in> UNIV"
    by auto
next
  show "\<And> s b . b <[ LPost id_l s b"
    by(auto simp add: id_l_def leq_refl)
next
  show "\<And>s b. b \<in> UNIV \<Longrightarrow> b = LUpd_Idem id_l s (LOut id_l s b) b"
    by(auto simp add: id_l_def leq_refl)
qed

(*
 * triv
 *)
definition triv_l ::
  "('x, 'a :: Bogus, 'a md_triv, ('x \<Rightarrow> 'a \<Rightarrow> 'a)) lifting" where
"triv_l =
  LMake (\<lambda> s a _ . mdt a) (\<lambda> s b . b) (\<lambda> s b . (case b of (mdt b') \<Rightarrow> b')) (\<lambda> s . mdt bogus) (\<lambda> f x . f x)"

interpretation triv_l : 
  lifting_valid_weak "(triv_l :: ('x, 'a :: Bogus, 'a md_triv , 'x \<Rightarrow> 'a \<Rightarrow> 'a) lifting)" "\<lambda> _ . UNIV"
proof
  fix s :: 'x
  fix a :: 'a
  fix b
  show "LOut (triv_l) s (LUpd_Idem (triv_l) s a b) = a"
    by(auto simp add:triv_l_def split:md_triv.splits)
next
  fix s b
  show "LOut triv_l s (LPost triv_l s b) = LOut triv_l s b"
    by(auto simp add: triv_l_def split: md_triv.splits)
next
  fix s a b
  show "LUpd_Idem triv_l s a b \<in> UNIV"
    by auto
next
  fix s b
  show "b \<in> UNIV \<Longrightarrow> LPost triv_l s b \<in> UNIV"
    by auto
next
  fix s b
  show "b <[ LPost triv_l s b"
    by(auto simp add: triv_l_def leq_refl)
next
  fix s b
  show "\<And>s b. b \<in> UNIV \<Longrightarrow> b = LUpd_Idem triv_l s (LOut triv_l s b) b"
    by(auto simp add: triv_l_def split: md_triv.splits)
qed

(* TODO: make sure that using the same namespace here hasn't cost us generality. *)
interpretation triv_l:
  lifting_valid_weak_ok "(triv_l :: ('x, 'a :: {Bogus, Okay}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
  show "\<And> S . ok_S \<subseteq> UNIV" by auto
next
  fix s a b
  show "b \<in> ok_S \<Longrightarrow> LUpd_Idem triv_l s a b \<in> ok_S"
    by(auto simp add: triv_l_def triv_ok_S)
next
  show "\<And>s b. b \<in> ok_S \<Longrightarrow> LPost triv_l s b \<in> ok_S"
    by(auto simp add: triv_l_def triv_ok_S)
qed


interpretation triv_l :
  lifting_valid_weak_pres "(triv_l :: ('x, 'a :: {Bogus}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
next
  fix v :: "'a md_triv"
  fix V 
  fix supr :: "'a md_triv"
  fix s 
  fix f

  assume Nemp : "v \<in> V"
  assume H : "is_sup V supr"

  show "is_sup (LMap_Idem triv_l f s ` V) (LMap_Idem triv_l f s supr)"
  proof(rule is_supI)
    fix x

    assume "x \<in> LMap_Idem triv_l f s ` V"

    then obtain x0 where X0 : "x0 \<in> V" "LMap_Idem triv_l f s x0 = x"
      by(auto)

    obtain x0' where X0' : "x0 = mdt x0'"
      by(cases x0; auto)

    obtain supr' where Supr' : "supr = mdt supr'"
      by(cases supr; auto)

    have Eq : "x0' = supr'"
      using is_supD1[OF H X0(1)] X0' Supr'
      by(auto simp add: triv_pleq)

    show "x <[ LMap_Idem triv_l f s supr"
      using X0' X0 Eq Supr'
      by(auto simp add: triv_pleq)
  next
    fix y
    assume Ub : "is_ub (LMap_Idem triv_l f s ` V) y"

    obtain y' where Y' : "y = mdt y'" by(cases y; auto)

    obtain v' where V' : "v = mdt v'" by(cases v; auto)

    have Eq1 : "y = LMap_Idem triv_l f s v"
      using is_ubE[OF Ub, of "LMap_Idem triv_l f s v"] Nemp
      by(auto simp add: triv_pleq)

    have  "supr = v"
      using is_supD1[OF H Nemp] by(auto simp add: triv_pleq)

    hence Eq2 : "LMap_Idem triv_l f s supr = LMap_Idem triv_l f s v" by simp

    show "LMap_Idem triv_l f s supr <[ y"
      using Eq1 Eq2
      by(simp add: triv_pleq)
  qed
next
  fix v :: "'a md_triv"
  fix V 
  fix supr :: "'a md_triv"
  fix s 
  fix f

  assume Nemp : "v \<in> V"
  assume H : "is_sup V supr"
  show "is_sup (LPost triv_l s ` V) (LPost triv_l s supr)"
  proof(rule is_supI)
    fix x

    assume "x \<in> LPost triv_l s ` V"

    then obtain x0 where X0 : "x0 \<in> V" "LPost triv_l s x0 = x"
      by(auto)

    obtain x0' where X0' : "x0 = mdt x0'"
      by(cases x0; auto)

    obtain supr' where Supr' : "supr = mdt supr'"
      by(cases supr; auto)

    have Eq : "x0' = supr'"
      using is_supD1[OF H X0(1)] X0' Supr'
      by(auto simp add: triv_pleq)

    show "x <[ LPost triv_l s supr"
      using X0' X0 Eq Supr'
      by(auto simp add: triv_pleq)
  next
    fix y
    assume Ub : "is_ub (LPost triv_l s ` V) y"

    obtain y' where Y' : "y = mdt y'" by(cases y; auto)

    obtain v' where V' : "v = mdt v'" by(cases v; auto)

    have Eq1 : "y = LPost triv_l s v"
      using is_ubE[OF Ub, of "LPost triv_l s v"] Nemp
      by(auto simp add: triv_pleq)

    have  "supr = v"
      using is_supD1[OF H Nemp] by(auto simp add: triv_pleq)

    hence Eq2 : "LPost triv_l s supr = LPost triv_l s v" by simp

    show "LPost triv_l s supr <[ y"
      using Eq1 Eq2
      by(simp add: triv_pleq)
  qed
qed

interpretation triv_l : lifting_valid_weak_ok_pres "(triv_l :: ('x, 'a :: {Bogus, Okay}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
qed


(*
 * option
 *)
definition option_l ::
  "('x, 'a, 'b, 'f) lifting \<Rightarrow> ('x, 'a, 'b option, 'f) lifting" where
"option_l t =
    LMake (\<lambda> s a b . 
              (case b of
                Some b' \<Rightarrow> Some (LUpd_Idem t s a b')
                | None \<Rightarrow> Some (LUpd_Idem t s a (LBase t s))))
          (\<lambda> s b .
              (case b of 
                Some b' \<Rightarrow> Some (LPost t s b')
                | None \<Rightarrow> Some (LPost t s (LBase t s))))
            (\<lambda> s b . (case b of Some b' \<Rightarrow> LOut t s b'
                        | None \<Rightarrow> LOut t s (LBase t s)))
            (\<lambda> s . None)
            (LFD t)"

definition option_l_S :: "('s, 'b) valid_set \<Rightarrow> ('s, 'b option) valid_set" where
"option_l_S S s = (Some ` S s)"


(* TODO: clean up mergeable instances so that we are consistently using Weakb instances
   where needed. *)
locale option_l_valid_weak = lifting_valid_weak

sublocale option_l_valid_weak \<subseteq> out : lifting_valid_weak_base "option_l l" "option_l_S S"
proof

  fix s a b
  show "LOut (option_l l) s (LUpd_Idem (option_l l) s a b) = a"
    using put_get
    by(auto simp add:option_l_def split:option.splits)
next
  show "\<And>s b. LOut (option_l l) s (LPost (option_l l) s b) =
           LOut (option_l l) s b"
    using post_nop 
    by(auto simp add:option_l_def option_l_S_def option_pleq split:option.splits)
next
  fix s :: 'a
  fix a
  fix b :: "'c option"
  show "LUpd_Idem (option_l l) s a b \<in> option_l_S S s"
    using put_S
    by(auto simp add: option_l_def option_l_S_def split:option.splits)
next
  fix s b
  assume "b \<in> option_l_S S s"
  then show "LPost (option_l l) s b \<in> option_l_S S s"
    using post_S
    by(auto simp add: option_l_def option_l_S_def)
next
  fix s b
  show "b <[ LPost (option_l l) s b"
    using post_geq
    by(cases b; auto simp add: option_l_def option_pleq)
next
  fix s b
  assume "b \<in> option_l_S S s"

  then show "b = LUpd_Idem (option_l l) s (LOut (option_l l) s b) b"
    using get_put_weak
    by(auto simp add: option_l_def option_l_S_def)
next
  fix s
  show "LBase (option_l l) s = \<bottom>"
    by(auto simp add: option_l_def option_bot)
qed

locale option_l_valid_weak_base = option_l_valid_weak

sublocale option_l_valid_weak_base \<subseteq> out: lifting_valid_weak_base "option_l l" "option_l_S S"
proof
qed

locale option_l_valid = lifting_valid + option_l_valid_weak

sublocale option_l_valid \<subseteq> param : lifting_valid_base "option_l l" "option_l_S S"
proof
  fix s a1 a2 b
  show "LUpd_Idem (option_l l) s a1 (LUpd_Idem (option_l l) s a2 b) =
       LUpd_Idem (option_l l) s a1 b"
    using put_put
    by(auto simp add:option_l_def option_l_S_def LNew_def option_pleq split:option.splits)
qed

locale option_l_valid_base = option_l_valid

locale option_l_valid_weak_base_ok = option_l_valid_weak_base + lifting_valid_weak_ok

sublocale option_l_valid_weak_base_ok \<subseteq> out : lifting_valid_weak_ok "option_l l" "option_l_S S"
proof
  fix s
  show "ok_S \<subseteq> option_l_S S s" using ok_S_valid
    by(auto simp add: option_l_S_def option_ok_S)
next
  fix s a b
  assume "(b :: 'c option) \<in> ok_S"
  then show "LUpd_Idem (option_l l) s a b \<in> ok_S"
    using ok_S_put
    by(auto simp add: option_l_S_def option_l_def option_ok_S split: option.splits)
next
  fix s b
  assume "(b :: 'c option) \<in> ok_S"
  then show "LPost (option_l l) s b \<in> ok_S"
    using ok_S_post
    by(auto simp add: option_l_S_def option_l_def option_ok_S split: option.splits)
qed

lemma is_sup_pair :
  assumes "a <[ b"
  shows "is_sup {a, b} b" using assms
  by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)


locale option_l_valid_weak_base_ok_pres =
  option_l_valid_weak_base_ok + lifting_valid_weak_pres

sublocale option_l_valid_weak_base_ok_pres \<subseteq> out : lifting_valid_weak_base_ok_pres "option_l l" "option_l_S S"
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

  show "is_sup (LMap_Idem (option_l l) f s ` V) (LMap_Idem (option_l l) f s supr)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap_Idem (option_l l) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap_Idem (option_l l) f s xo = x"
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

    hence Conc' : "is_sup (LMap_Idem l f s ` {xo', supr'}) (LMap_Idem l f s supr')"
      using Xo' Supr' pres[of xo' "{xo', supr'}" s supr' f] 
      by auto

    thus "x <[ LMap_Idem (option_l l) f s supr"
      using is_supD1[OF Conc', of x'] X' Xo Xo' Supr'
      by(cases l; auto simp add: option_l_def option_pleq)
  next

    fix z

    assume Ub : "is_ub (LMap_Idem (option_l l) f s ` V) z" 

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

    have Supr'_sup : "is_sup (LMap_Idem l f s ` V') (LMap_Idem l f s supr')"
      using pres[OF V'(2) SV'(2) Supr'_sup, of f] Supr'(2)
      by auto

    obtain vr' where Vr' : "LMap_Idem (option_l l) f s v = Some vr'"
      using put_get V'
      by(cases l; auto simp add: option_l_def)

    have "LMap_Idem (option_l l) f s v <[ z"
      using is_ubE[OF Ub, of "LMap_Idem (option_l l) f s v"] Nemp
      by(auto)

    then obtain z' where Z' : "z = Some z'" using Vr'
      by(cases z; auto simp add: option_pleq)

    hence "is_ub (LMap_Idem l f s ` V') z'"
      using Ub SV'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)

    hence "LMap_Idem l f s supr' <[ z'"
      using is_supD2[OF Supr'_sup] by auto

    then show "LMap_Idem (option_l l) f s supr <[ z" using V' Z' Supr'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)
  qed
next
  fix V
  fix s 
  fix v supr :: "'c option"

  assume Nemp : "v \<in> V"
  assume V_valid : "V \<subseteq> option_l_S S s"

  assume Hsup : "is_sup V supr"
  assume Hsup_in : "supr \<in> option_l_S S s"

  obtain supr' where Supr' : "supr = Some supr'" "supr' \<in> S s"
    using V_valid Hsup_in by(auto simp add: option_l_S_def)

  show "is_sup (LPost (option_l l) s ` V) (LPost (option_l l) s supr)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LPost (option_l l) s ` V"

    then obtain xo where Xo : "xo \<in> V" "LPost (option_l l) s xo = x"
      by auto

    have "xo <[ supr" using is_supD1[OF Hsup Xo(1)] by simp

    obtain xo' where Xo' : "xo = Some xo'" "xo' \<in> S s" using V_valid Xo
      by(auto simp add: option_l_S_def)

    have "x \<in> option_l_S S s"
      using post_S[OF Xo'(2)] Xo Xo'
      by(auto simp add: option_l_S_def option_l_def split: option.splits)

    then obtain x' where X' : "x = Some x'" "x' \<in> S s"
      by(auto simp add: option_l_S_def)


    have "xo' <[ supr'" using Xo' Supr' `xo <[ supr`
      by(simp add: option_pleq)

    hence "is_sup {xo', supr'} supr'"
      using is_sup_pair by auto

    hence Conc' : "is_sup (LPost l s ` {xo', supr'}) (LPost l s supr')"
      using Xo Xo' Supr' pres_post[of xo' "{xo', supr'}" s supr'] 
      by auto

    thus "x <[ LPost (option_l l) s supr"
      using is_supD1[OF Conc', of x'] X' Xo Xo' Supr'
      by(cases l; auto simp add: option_l_def option_pleq)
  next

    fix z

    assume Ub : "is_ub (LPost (option_l l) s ` V) z" 

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

    have Supr'_sup : "is_sup (LPost l s ` V') (LPost l s supr')"
      using pres_post[OF V'(2) SV'(2) Supr'_sup] Supr'(2)
      by auto

    obtain vr' where Vr' : "LPost (option_l l) s v = Some vr'"
      using put_get V'
      by(cases l; auto simp add: option_l_def)

    have "LPost (option_l l) s v <[ z"
      using is_ubE[OF Ub, of "LPost (option_l l) s v"] Nemp
      by(auto)

    then obtain z' where Z' : "z = Some z'" using Vr'
      by(cases z; auto simp add: option_pleq)

    hence "is_ub (LPost l s ` V') z'"
      using Ub SV'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)

    hence "LPost l s supr' <[ z'"
      using is_supD2[OF Supr'_sup] by auto

    then show "LPost (option_l l) s supr <[ z" using V' Z' Supr'
      by(cases l; auto simp add: option_l_def is_ub_def option_pleq)
  qed

next
  show "\<And> s . \<bottom> \<notin> option_l_S S s"
    by(auto simp add: option_l_S_def option_bot)
qed

locale option_l_valid_base_ok_pres =
  option_l_valid_weak_base_ok_pres + option_l_valid

sublocale option_l_valid_base_ok_pres \<subseteq> out : lifting_valid_base_ok_pres "option_l l" "option_l_S S"
proof
qed

(*
 * prio
 *)
definition prio_l ::
 "('x \<Rightarrow> nat) \<Rightarrow>
  ('x \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow>
  ('x, 'a, 'b, 'f ) lifting\<Rightarrow>
  ('x, 'a, 'b md_prio, 'f) lifting" where
"prio_l f0 f1 t =
      LMake (\<lambda> s a b . (case b of
                             mdp m b' \<Rightarrow> mdp m (LUpd_Idem t s a b')))
            (\<lambda> s b . (case b of
                             mdp m b' \<Rightarrow> mdp (f1 s m) (LPost t s b')))
            (\<lambda> s p . (case p of
                       mdp m b \<Rightarrow> LOut t s b))
            (\<lambda> s . mdp (f0 s) (LBase t s))
            (LFD t)"

definition prio_l_S :: "('x, 'b) valid_set \<Rightarrow> ('x, 'b md_prio) valid_set" where
"prio_l_S S s =
  { p . (case p of
          mdp n x \<Rightarrow> x \<in> S s) }"

locale prio_l_valid_weak' =
  fixes l :: "('syn, 'a, 'b, 'f) lifting"
  fixes S :: "'syn \<Rightarrow> 'b set"
  fixes f0 :: "'syn \<Rightarrow> nat"
  fixes f1 :: "'syn \<Rightarrow> nat \<Rightarrow> nat"
  assumes f1_nondecrease : "\<And> s p . p \<le> f1 s p"


locale prio_l_valid_weak = prio_l_valid_weak' + lifting_valid_weak

sublocale prio_l_valid_weak \<subseteq> out : lifting_valid_weak "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a b
  show "LOut (prio_l f0 f1 l) s (LUpd_Idem (prio_l f0 f1 l) s a b) = a"
    using put_get
    by(auto simp add:prio_l_def LNew_def split:md_prio.splits)
next
  fix s b
  show "LOut (prio_l f0 f1 l) s (LPost (prio_l f0 f1 l) s b) =
           LOut (prio_l f0 f1 l) s b"
    using post_nop
    by(auto simp add:prio_l_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s a b
  show "LUpd_Idem (prio_l f0 f1 l) s a b \<in> prio_l_S S s"
    using put_S
    by(auto simp add:prio_l_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s b
  assume Hb : "b \<in> prio_l_S S s"
  then show "LPost (prio_l f0 f1 l) s b \<in> prio_l_S S s"
    using post_S
    by(auto simp add:prio_l_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s b
  show "b <[ LPost (prio_l f0 f1 l) s b"
    using post_geq f1_nondecrease
    by(auto simp add:prio_l_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
next
  fix s b
  assume "b \<in> prio_l_S S s"
  then show "b = LUpd_Idem (prio_l f0 f1 l) s (LOut (prio_l f0 f1 l) s b) b"
    using get_put_weak
    by(auto simp add:prio_l_def prio_l_S_def LNew_def prio_pleq split:md_prio.splits)
qed

locale prio_l_valid = prio_l_valid_weak + lifting_valid

sublocale prio_l_valid \<subseteq> out : lifting_valid "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a1 a2
  fix b :: "'c md_prio"

  obtain b' pb'  where B' : "b = mdp pb' b'"
    by(cases b; auto)

  show "LUpd_Idem (prio_l f0 f1 l) s a1
        (LUpd_Idem (prio_l f0 f1 l) s a2 b) =
       LUpd_Idem (prio_l f0 f1 l) s a1 b"
    using put_put B' f1_nondecrease
    by(auto simp add: prio_l_def prio_pleq)
qed

locale prio_l_valid_strong' =
  fixes l :: "('syn, 'a, ('b :: Pord_Weak), 'f) lifting"
  fixes S :: "'syn \<Rightarrow> 'b set"
  fixes f0 :: "'syn \<Rightarrow> nat"
  fixes f1 :: "'syn \<Rightarrow> nat \<Rightarrow> nat"
  assumes f1_increase : "\<And> s p . p < f1 s p"

locale prio_l_valid_stronger' = prio_l_valid_strong' +
  fixes S' :: "('syn \<Rightarrow> ('b :: Pord_Weak) md_prio set)"
  assumes S' : "\<And> x . prio_l_S S x \<subseteq> S' x"

locale prio_l_valid_base' =
  fixes l :: "('syn, 'a, ('b :: Pord_Weakb), 'f) lifting"
  fixes S :: "('syn \<Rightarrow> 'b set)"
  fixes f0 :: "'syn \<Rightarrow> nat"
  assumes zero : "\<And> s . f0 s = 0"

locale prio_l_valid_weak_base = prio_l_valid_weak + lifting_valid_weak_base + prio_l_valid_base'

sublocale prio_l_valid_weak_base \<subseteq> out : lifting_valid_weak_base "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s
  show "LBase (prio_l f0 f1 l) s = \<bottom>"
    using zero base
    by(auto simp add: prio_l_def prio_bot)
qed

locale prio_l_valid_base = prio_l_valid + prio_l_valid_weak_base

locale prio_l_valid_weak_ok = prio_l_valid_weak + lifting_valid_weak_ok

sublocale prio_l_valid_weak_ok \<subseteq> out : lifting_valid_weak_ok "(prio_l f0 f1 l)" "(prio_l_S S)"
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

  show "LUpd_Idem (prio_l f0 f1 l) s a b \<in> ok_S"
    using ok_S_put[OF H'] B'
    by(auto simp add: prio_l_S_def prio_l_def prio_ok_S)
next
  fix s
  fix b :: "'c md_prio"
  assume H: "b \<in> ok_S"

  obtain b' pb' where B' : "b = mdp pb' b'"
    by(cases b; auto)

  have H' : "b' \<in> ok_S"
    using H B'
    by(auto simp add: prio_l_S_def prio_ok_S)

  show "LPost (prio_l f0 f1 l) s b \<in> ok_S"
    using ok_S_post[OF H'] B'
    by(auto simp add: prio_l_S_def prio_l_def prio_ok_S)
qed

locale prio_l_valid_weak_base_ok = prio_l_valid_weak_ok + prio_l_valid_weak_base

sublocale prio_l_valid_weak_base_ok \<subseteq> out : lifting_valid_weak_base_ok "(prio_l f0 f1 l)" "(prio_l_S S)"
proof
qed

locale prio_l_valid_ok = prio_l_valid_weak_ok + prio_l_valid

sublocale prio_l_valid_ok \<subseteq> out : lifting_valid_ok "(prio_l f0 f1 l)" "(prio_l_S S)"
proof
qed

locale prio_l_valid_base_ok = prio_l_valid_ok + prio_l_valid_weak_base_ok
sublocale  prio_l_valid_base_ok \<subseteq> out : lifting_valid_base_ok "(prio_l f0 f1 l)" "(prio_l_S S)"
proof
qed


(* finally, facts about pres *)

locale prio_l_valid_weak_ok_pres' =
  fixes l :: "('syn, 'a, ('b :: Pord), 'f) lifting"
  fixes f0 :: "'syn \<Rightarrow> nat"
  fixes f1 :: "'syn \<Rightarrow> nat \<Rightarrow> nat"
  assumes f1_mono_leq : "\<And> s p1 p2 . p1 \<le> p2 \<Longrightarrow> f1 s p1 \<le> f1 s p2"
  assumes f1_mono_lt : "\<And> s p1 p2 . p1 < p2 \<Longrightarrow> f1 s p1 < f1 s p2"

(* the way we proved this theorem, we actually need base for it to be true.
 * as well as strength. *)

(* TODO: the structure of this theorem is a bit different now. but i'm pretty sure it still holds. *)
locale prio_l_valid_base_ok_pres = prio_l_valid_weak_ok_pres' + prio_l_valid_base_ok + lifting_valid_base_ok_pres
sublocale prio_l_valid_base_ok_pres \<subseteq> out : lifting_valid_base_ok_pres "prio_l f0 f1 l" "prio_l_S S"
  sorry
(*
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

  obtain supr_res' psupr_res' where Result : "LMap_Idem (prio_l f0 f1 l) f s supr = mdp psupr_res' supr_res'"
    by(cases "LMap_Idem (prio_l f0 f1 l) f s supr"; auto)

  show "is_sup (LMap_Idem (prio_l f0 f1 l) f s ` V) (LMap_Idem (prio_l f0 f1 l) f s supr)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap_Idem (prio_l f0 f1 l) f s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap_Idem (prio_l f0 f1 l) f s xo = x"
      by auto

    have "xo <[ supr" using is_supD1[OF Hsup Xo(1)] by simp

    have "x \<in> prio_l_S S s" 
      using put_S Xo
      by(cases l; auto simp add: prio_l_S_def prio_l_def split: md_prio.splits)

    then obtain x' px' where X' : "x = mdp px' x'" "x' \<in> S s"
      by(auto simp add: prio_l_S_def split: md_prio.splits)

    obtain xo' pxo' where Xo' : "xo = mdp pxo' xo'" "xo' \<in> S s" using Xo Vsubs
      by(cases xo; auto simp add: prio_l_S_def split: md_prio.splits)

    show "x <[ LMap_Idem (prio_l f0 f1 l) f s supr"
    proof(cases "pxo' = psupr'")
      case True

      then have "xo' <[ supr'" using Xo' Supr' `xo <[ supr`
        by(simp add: prio_pleq)

      hence "is_sup {xo', supr'} supr'"
        using is_sup_pair by auto
  
      hence Conc' : "is_sup (LMap_Idem l f s ` {xo', supr'}) (LMap_Idem l f s supr')"
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

    assume Ub : "is_ub (LMap_Idem (prio_l f0 f1 l) f s ` V) zo" 

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
    show "LMap_Idem (prio_l f0 f1 l) f s supr <[ zo"
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

      have Supr'_sup_vmax : "is_sup (LMap_Idem l f s ` Vmaxv) (LMap_Idem l f s supr')"
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
      then show "LMap_Idem (prio_l f0 f1 l) f s supr <[ zo"
      proof cases
        case L

        have "m \<in> V"
          using M VSmax by auto
        
        have Bad : "LMap_Idem (prio_l f0 f1 l) f s m \<in> LMap_Idem (prio_l f0 f1 l) f s ` V"
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
*)

(* NB: "stronger" version of prio_l does not work with pres, because we need to know that
 * we are actually in prio_l_S S, not some superset.
 *)

(* Several useful examples of instantiating prio_l.
*)
definition prio_l_keep :: "('x, 'a, 'b :: Pord, 'f) lifting \<Rightarrow> ('x, 'a, 'b md_prio, 'f) lifting" where
"prio_l_keep =
  prio_l (\<lambda> _ . 0) (\<lambda> _ n . n)"

definition prio_l_inc :: "('x, 'a, 'b :: Pord, 'f) lifting \<Rightarrow> ('x, 'a, 'b md_prio, 'f) lifting" where
"prio_l_inc =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 1 + x)"

definition prio_l_inc2 :: "('x, 'a, 'b :: Pord, 'f) lifting \<Rightarrow> ('x, 'a, 'b md_prio, 'f) lifting" where
"prio_l_inc2 =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 2 + x)"

definition prio_l_inc3 :: "('x, 'a, 'b :: Pord, 'f) lifting \<Rightarrow> ('x, 'a, 'b md_prio, 'f) lifting" where
"prio_l_inc3 =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . 3  + x)"

definition prio_l_incN :: "nat \<Rightarrow> ('x, 'a, 'b :: Pord, 'f) lifting \<Rightarrow> ('x, 'a, 'b md_prio, 'f) lifting" where
"prio_l_incN n =
  prio_l (\<lambda> _ . 0) (\<lambda> _ x . n + x)"

definition prio_l_case_inc :: "('x \<Rightarrow> nat) \<Rightarrow> ('x, 'a, 'b :: Pord, 'f) lifting \<Rightarrow> ('x, 'a, 'b md_prio, 'f) lifting" where
"prio_l_case_inc f =
  prio_l (\<lambda> _ . 0) (\<lambda> s x . (f s) + x)"

(*
 * fst
 *)

definition fst_l ::
  "('x, 'a, 'b1 :: Pord_Weak, 'f) lifting \<Rightarrow>
   ('x, 'a, 'b1 * ('b2 :: Pord_Weakb), 'f) lifting" where
"fst_l t =
  LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (LUpd_Idem t s a b1, b2)))
            (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> (LPost t s b1, b2)))
            (\<lambda> s x . (LOut t s (fst x)))
            (\<lambda> s . (LBase t s, \<bottom>))
            (LFD t)"

definition fst_l_S :: "('x, 'b1 :: Pord_Weak) valid_set \<Rightarrow> ('x, ('b1 * 'b2 :: Pord_Weakb)) valid_set" where
"fst_l_S S s =
  { b . case b of (b1, _) \<Rightarrow> (b1 \<in> S s) }"

locale fst_l_valid_weak = lifting_valid_weak

sublocale fst_l_valid_weak \<subseteq> out : lifting_valid_weak "fst_l l" "fst_l_S S"
  sorry
(*
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
*)
locale fst_l_valid = fst_l_valid_weak + lifting_valid

sublocale fst_l_valid \<subseteq> out : lifting_valid "fst_l l" "fst_l_S S"
  sorry
(*
proof
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  (*assume  Hb : "b \<in> fst_l_S S s"*)
  show "b <[ LUpd (fst_l l) s a b"
    using get_put
    by(auto simp add: fst_l_def prod_pleq fst_l_S_def leq_refl split:prod.splits)
qed
*)


locale fst_l_valid_weak_base = fst_l_valid_weak +   lifting_valid_weak_base
sublocale fst_l_valid_weak_base \<subseteq> out : lifting_valid_weak_base "fst_l l" "fst_l_S S"
proof
  fix s
  show "LBase (fst_l l) s = \<bottom>" using base
    by(auto simp add: fst_l_def prod_bot)
qed

locale fst_l_valid_base = fst_l_valid + fst_l_valid_weak_base
sublocale fst_l_valid_base \<subseteq> out : lifting_valid_base "fst_l l" "fst_l_S S"
proof
qed

locale fst_l_valid_weak_ok = fst_l_valid_weak + lifting_valid_weak_ok
sublocale fst_l_valid_weak_ok \<subseteq> out : lifting_valid_weak_ok "fst_l l" "fst_l_S S"
  sorry
(*
proof
  fix s

  show "ok_S \<subseteq> fst_l_S S s" using ok_S_valid
    by(auto simp add: prod_ok_S fst_l_S_def)
next
  fix s a
  fix b :: "('c * 'e)"
  assume B: "b \<in> ok_S" 
  then show "LUpd (fst_l l) s a b \<in> ok_S" using ok_S_put
    by(auto simp add: fst_l_def prod_ok_S)
qed
*)

locale fst_l_valid_ok = fst_l_valid + fst_l_valid_weak_ok
sublocale fst_l_valid_ok \<subseteq> lifting_valid_ok "fst_l l" "fst_l_S S"
proof
qed

locale fst_l_valid_weak_base_ok = fst_l_valid_weak_ok + fst_l_valid_weak_base
sublocale fst_l_valid_weak_base_ok \<subseteq> out : lifting_valid_weak_base_ok "fst_l l" "fst_l_S S"
proof
qed

locale fst_l_valid_base_ok = fst_l_valid_ok + fst_l_valid_base
sublocale fst_l_valid_base_ok \<subseteq> out : lifting_valid_base_ok "fst_l l" "fst_l_S S"
proof
qed

locale fst_l_valid_weak_pres = fst_l_valid_weak + lifting_valid_weak_pres
sublocale fst_l_valid_weak_pres \<subseteq> out : lifting_valid_weak_pres "fst_l l" "fst_l_S S"
  sorry
(*
proof
  fix v supr :: "('c * 'e)"
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
*)
locale fst_l_valid_pres = fst_l_valid_weak_pres + fst_l_valid
sublocale fst_l_valid_pres \<subseteq> out : lifting_valid_pres "fst_l l" "fst_l_S S"
proof
qed

locale fst_l_valid_weak_base_pres = fst_l_valid_weak_base + fst_l_valid_weak_pres + lifting_valid_weak_base_pres
sublocale fst_l_valid_weak_base_pres \<subseteq> out : lifting_valid_weak_base_pres "fst_l l" "fst_l_S S"
proof
  fix s
  show "\<bottom> \<notin> fst_l_S S s"
    using bot_bad[of s]
    by(auto simp add: fst_l_S_def prod_bot)
qed

locale fst_l_valid_base_pres = fst_l_valid_pres + fst_l_valid_weak_base_pres
sublocale fst_l_valid_base_pres \<subseteq> out : lifting_valid_base_pres "fst_l l" "fst_l_S S"
proof qed

locale fst_l_valid_weak_ok_pres = fst_l_valid_weak_pres + fst_l_valid_weak_ok
sublocale fst_l_valid_weak_ok_pres \<subseteq> out : lifting_valid_weak_ok_pres "fst_l l" "fst_l_S S"
proof qed

locale fst_l_valid_ok_pres = fst_l_valid_pres + fst_l_valid_ok
sublocale fst_l_valid_ok_pres \<subseteq> out : lifting_valid_ok_pres "fst_l l" "fst_l_S S"
proof qed

locale fst_l_valid_weak_base_ok_pres = fst_l_valid_weak_base_pres + fst_l_valid_weak_ok
sublocale fst_l_valid_weak_base_ok_pres \<subseteq> out: lifting_valid_weak_base_ok_pres "fst_l l" "fst_l_S S"
proof qed

locale fst_l_valid_base_ok_pres = fst_l_valid_base_pres + fst_l_valid_base_ok
sublocale fst_l_valid_base_ok_pres \<subseteq> out : lifting_valid_base_ok_pres "fst_l l" "fst_l_S S"
proof qed

(*
 * snd
 *)

definition snd_l ::
  "('x, 'a, 'b2 :: Pord_Weak, 'f) lifting \<Rightarrow>
   ('x, 'a, ('b1 :: Pord_Weakb) * 'b2, 'f) lifting" where
"snd_l t =
      LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (b1, LUpd_Idem t s a b2)))
            (\<lambda> s b . (case b of (b1, b2) \<Rightarrow> (b1, LPost t s b2)))
            (\<lambda> s x . (LOut t s (snd x)))
            (\<lambda> s . (\<bottom>, LBase t s))
            (LFD t)"

definition snd_l_S :: "('x, 'b2 :: Pord_Weak) valid_set \<Rightarrow> ('x, ('b1 :: Pord_Weakb * 'b2)) valid_set" where
"snd_l_S S s =
  { b . case b of (_, b2) \<Rightarrow> (b2 \<in> S s) }"


locale snd_l_valid_weak = lifting_valid_weak

sublocale snd_l_valid_weak \<subseteq> out : lifting_valid_weak "snd_l l" "snd_l_S S"
  sorry
(*
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
*)

locale snd_l_valid = snd_l_valid_weak + lifting_valid

sublocale snd_l_valid \<subseteq> out : lifting_valid "snd_l l" "snd_l_S S"
  sorry
(*
proof
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  (*assume  Hb : "b \<in> snd_l_S S s"*)
  show "b <[ LUpd (snd_l l) s a b"
    using get_put
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
qed
*)

locale snd_l_valid_weak_base = snd_l_valid_weak +   lifting_valid_weak_base
sublocale snd_l_valid_weak_base \<subseteq> out : lifting_valid_weak_base "snd_l l" "snd_l_S S"
proof
  fix s
  show "LBase (snd_l l) s = \<bottom>" using base
    by(auto simp add: snd_l_def prod_bot)
qed

locale snd_l_valid_base = snd_l_valid + snd_l_valid_weak_base
sublocale snd_l_valid_base \<subseteq> out : lifting_valid_base "snd_l l" "snd_l_S S"
proof
qed

locale snd_l_valid_weak_ok = snd_l_valid_weak + lifting_valid_weak_ok
sublocale snd_l_valid_weak_ok \<subseteq> out : lifting_valid_weak_ok "snd_l l" "snd_l_S S"
  sorry
(*
proof
  fix s

  show "ok_S \<subseteq> snd_l_S S s" using ok_S_valid
    by(auto simp add: prod_ok_S snd_l_S_def)
next
  fix s a
  fix b :: "('e * 'c)"
  assume B: "b \<in> ok_S" 
  then show "LUpd (snd_l l) s a b \<in> ok_S" using ok_S_put
    by(auto simp add: prod_ok_S snd_l_S_def snd_l_def)
qed
*)

locale snd_l_valid_ok = snd_l_valid + snd_l_valid_weak_ok
sublocale snd_l_valid_ok \<subseteq> lifting_valid_ok "snd_l l" "snd_l_S S"
proof
qed

locale snd_l_valid_weak_base_ok = snd_l_valid_weak_ok + snd_l_valid_weak_base
sublocale snd_l_valid_weak_base_ok \<subseteq> out : lifting_valid_weak_base_ok "snd_l l" "snd_l_S S"
proof
qed

locale snd_l_valid_base_ok = snd_l_valid_ok + snd_l_valid_base
sublocale snd_l_valid_base_ok \<subseteq> out : lifting_valid_base_ok "snd_l l" "snd_l_S S"
proof
qed

locale snd_l_valid_weak_pres = snd_l_valid_weak + lifting_valid_weak_pres
sublocale snd_l_valid_weak_pres \<subseteq> out : lifting_valid_weak_pres "snd_l l" "snd_l_S S"
  sorry
(*
proof
  fix v supr :: "('e * 'c)"
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
*)
locale snd_l_valid_pres = snd_l_valid_weak_pres + snd_l_valid
sublocale snd_l_valid_pres \<subseteq> out : lifting_valid_pres "snd_l l" "snd_l_S S"
proof
qed

locale snd_l_valid_weak_base_pres = snd_l_valid_weak_base + snd_l_valid_weak_pres + lifting_valid_weak_base_pres
sublocale snd_l_valid_weak_base_pres \<subseteq> out : lifting_valid_weak_base_pres "snd_l l" "snd_l_S S"
proof
  fix s
  show "\<bottom> \<notin> snd_l_S S s"
    using bot_bad[of s]
    by(auto simp add: snd_l_S_def prod_bot)
qed

locale snd_l_valid_base_pres = snd_l_valid_pres + snd_l_valid_weak_base_pres
sublocale snd_l_valid_base_pres \<subseteq> out : lifting_valid_base_pres "snd_l l" "snd_l_S S"
proof qed

locale snd_l_valid_weak_ok_pres = snd_l_valid_weak_pres + snd_l_valid_weak_ok
sublocale snd_l_valid_weak_ok_pres \<subseteq> out : lifting_valid_weak_ok_pres "snd_l l" "snd_l_S S"
proof qed

locale snd_l_valid_ok_pres = snd_l_valid_pres + snd_l_valid_ok
sublocale snd_l_valid_ok_pres \<subseteq> out : lifting_valid_ok_pres "snd_l l" "snd_l_S S"
proof qed

locale snd_l_valid_weak_base_ok_pres = snd_l_valid_weak_base_pres + snd_l_valid_weak_ok
sublocale snd_l_valid_weak_base_ok_pres \<subseteq> out: lifting_valid_weak_base_ok_pres "snd_l l" "snd_l_S S"
proof
qed

locale snd_l_valid_base_ok_pres = snd_l_valid_base_pres + snd_l_valid_base_ok
sublocale snd_l_valid_base_ok_pres \<subseteq> out : lifting_valid_base_ok_pres "snd_l l" "snd_l_S S"
proof qed


(*
 * merge (new ! !)
 * note that this definition is going to behave weirdly on non-compatible liftings.
 *)

definition merge_l ::
  "('x, 'a1, 'b :: Mergeable, 'f1) lifting \<Rightarrow>
   ('x, 'a2, 'b :: Mergeable, 'f2) lifting \<Rightarrow>
   ('x, 'a1 * 'a2, 'b, 'f1 * 'f2) lifting" where
"merge_l t1 t2 =
    LMake
      (\<lambda> s a b . 
        (case a of (a1, a2) \<Rightarrow>
          (let supr = [^ LUpd t1 s a1 b, LUpd t2 s a2 b ^] in
           let o1 = LOut t1 s supr in
           let o2 = LOut t2 s supr in
           [^ LUpd_Idem t1 s o1 b, LUpd_Idem t2 s o2 b ^]
          )))
      (\<lambda> s b . [^ LPost t1 s b, LPost t2 s b ^])
      (\<lambda> s b . (LOut t1 s b, LOut t2 s b))
      (\<lambda> s . [^ LBase t1 s, LBase t2 s ^] )
      (\<lambda> f1f2 s a1a2 .
          case f1f2 of (f1, f2) \<Rightarrow>
          (case a1a2 of (a1, a2) \<Rightarrow>
            (LFD t1 f1 s a1, LFD t2 f2 s a2)))"

locale merge_l_valid_weak' = 
  fixes l1 :: "('x, 'a1, 'b :: Mergeable, 'f1) lifting" 
  fixes l2 :: "('x, 'a2, 'b :: Mergeable, 'f2) lifting"

locale merge_l_valid_weak =
  merge_l_valid_weak' +
  l_ortho +
  in1 : lifting_valid_weak l1 S1 +
  in2 : lifting_valid_weak l2 S2

lemma sup_to_bsup :
  assumes H: "is_sup {a, b} c"
  shows "[^ a, b ^] = c"
  using is_sup_unique[OF bsup_sup[OF H bsup_spec] H]
  by auto

sublocale merge_l_valid_weak \<subseteq> out : lifting_valid_weak "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s
  fix a :: "'b * 'e"
  fix b :: "'c"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have BB : "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  hence BB' : "has_sup {b, b}"
    by(auto simp add: has_sup_def)

  obtain supr1 where Supr1 : 
    "is_sup { LUpd_Idem l1 s a1 b, LUpd_Idem l2 s a2 b } supr1"
    using compat_idem[OF BB]
    by(fastforce simp add: has_sup_def)

  have Eq1 : "[^ LUpd_Idem l1 s a1 b, LUpd_Idem l2 s a2 b ^] = supr1"
    using is_sup_unique[OF bsup_sup[OF Supr1 bsup_spec] Supr1] by simp

  obtain supr2 where Supr2 :
    "is_sup {LPost l1 s (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b)} supr2"
    using compat_post[OF Supr1]
    by(fastforce simp add: has_sup_def)

  have Eq2 : "[^LPost l1 s (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b) ^] = supr2"
    using is_sup_unique[OF bsup_sup[OF Supr2 bsup_spec] Supr2] by simp

  have GetL1 : "LOut l1 s [^LPost l1 s (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b) ^] = a1"
    using compat_post_get1[OF Supr1 Supr2] Supr1
    using compat_idem_get1[OF BB Supr1]
    unfolding Eq2
    by(simp)

  have GetL2 : "LOut l2 s [^LPost l1 s (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b) ^] = a2"
    using compat_post_get2[OF Supr1 Supr2] Supr1
    using compat_idem_get2[OF BB Supr1]
    unfolding Eq2
    by(simp)

  have GetL1' : "LOut l1 s [^ LUpd_Idem l1 s a1 b, LUpd_Idem l2 s a2 b ^] = a1"
    using compat_idem_get1[OF BB Supr1] unfolding Eq1
    by auto

  have GetL2' : "LOut l2 s [^ LUpd_Idem l1 s a1 b, LUpd_Idem l2 s a2 b ^] = a2"
    using compat_idem_get2[OF BB Supr1] unfolding Eq1
    by auto
  
  show "LOut (merge_l l1 l2) s (LUpd_Idem (merge_l l1 l2) s a b) = a" 
    unfolding A merge_l_def
    by(simp add: Let_def GetL1 GetL2 GetL1' GetL2')
next

  fix s
  fix b :: 'c

  have BB : "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain supr1 where Supr1: "is_sup { LPost l1 s b, LPost l2 s b } supr1"
    using compat_post[OF BB]
    by(fastforce simp add: has_sup_def)

  have Eq1 : "[^ LPost l1 s b, LPost l2 s b ^] = supr1"
    using sup_to_bsup[OF Supr1]
    by auto

  have OutL1 : "LOut l1 s supr1 = LOut l1 s b"
    using compat_post_get1[OF BB Supr1]
    by simp

  have OutL2 : "LOut l2 s supr1 = LOut l2 s b"
    using compat_post_get2[OF BB Supr1]
    by simp

  show " LOut (merge_l l1 l2) s (LPost (merge_l l1 l2) s b) = LOut (merge_l l1 l2) s b"
    using OutL1 OutL2
    by(simp add: merge_l_def Eq1)
next
  fix s 
  fix a :: "'b * 'e"
  fix b :: 'c

  obtain a1 a2 where A:
    "a = (a1, a2)"
    by(cases a; auto)

  have BB : "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain sup1 where Sup1 :
    "is_sup {LUpd_Idem l1 s
        (LOut l1 s
          [^ LPost l1 s
              (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b) ^])
        b, LUpd_Idem l2 s
            (LOut l2 s
              [^ LPost l1 s
                  (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b) ^])
            b} sup1"
    using compat_idem[OF BB]
    by (fastforce simp add: has_sup_def)

  then have Bsup1 : "[^LUpd_Idem l1 s
        (LOut l1 s
          [^ LPost l1 s
              (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b) ^])
        b, LUpd_Idem l2 s
            (LOut l2 s
              [^ LPost l1 s
                  (LUpd_Idem l1 s a1 b), LPost l2 s (LUpd_Idem l2 s a2 b) ^])
            b ^] = sup1"
    using sup_to_bsup[OF Sup1]
    by auto

  show "LUpd_Idem (merge_l l1 l2) s a b \<in> S1 s \<inter> S2 s" unfolding A
    using compat_idem_S[OF BB Sup1] Bsup1
    by(auto simp add: merge_l_def Let_def)
next

  fix s
  fix b :: 'c

  assume B_in : "b \<in> S1 s \<inter> S2 s"

  have BB : "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain sup1 where Sup1 : "is_sup { LPost l1 s b, LPost l2 s b } sup1"
    using compat_post[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsup1 : "[^ LPost l1 s b, LPost l2 s b ^] = sup1"
    using sup_to_bsup[OF Sup1]
    by simp

  have Sup1_in : "sup1 \<in> S1 s \<inter> S2 s"
    using compat_post_S[OF BB _ _ Sup1] B_in
    by auto

  then show "LPost (merge_l l1 l2) s b \<in> S1 s \<inter> S2 s"
    using Bsup1
    by(auto simp add: merge_l_def Let_def)
next

  fix s
  fix b :: 'c

  have "b <[ LPost l1 s b"
    using in1.post_geq
    by auto

  then have "LPost l1 s b <[ [^ LPost l1 s b, LPost l2 s b ^]"
    using is_bsupD1[OF bsup_spec]
    by(auto)

  then have "b <[ [^ LPost l1 s b, LPost l2 s b ^]"
    using leq_trans[OF `b <[ LPost l1 s b`]
    by auto

  then show "b <[ LPost (merge_l l1 l2) s b"
    by(auto simp add: merge_l_def Let_def)
next
  fix s
  fix b :: 'c

  assume B_in : "b \<in> S1 s \<inter> S2 s"

  then have B_in1 : "b \<in> S1 s" and B_in2 : "b \<in> S2 s"
    by auto

  have BB : "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

(* [^ LPost l1 s (LUpd_Idem l1 s (LOut l1 s b) b), LPost l2 s (LUpd_Idem l2 s (LOut l2 s b) b) ^] *)

  have Eq1_1 : "LUpd_Idem l1 s (LOut l1 s b) b = b"
    using in1.get_put_weak[OF B_in1] by auto

  have Eq1_2 : "LUpd_Idem l2 s (LOut l2 s b) b = b"
    using in2.get_put_weak[OF B_in2] by auto

  obtain sup1 where Sup1 : "is_sup {LPost l1 s b, LPost l2 s b } sup1"
    using compat_post[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsup1 : "[^ LPost l1 s b, LPost l2 s b ^] = sup1"
    using sup_to_bsup[OF Sup1]
    by auto

  have Eq2_1 : "LOut l1 s sup1 = LOut l1 s b"
    using compat_post_get1[OF BB Sup1] by auto

  have Eq2_2 : "LOut l2 s sup1 = LOut l2 s b"
    using compat_post_get2[OF BB Sup1] by auto

(*
  obtain sup1 where Sup1 : "is_sup {LUpd_Idem l1 s (LOut l1 s b) b, LUpd_Idem l2 s (LOut l2 s b) b} sup1"
    using compat_idem[OF BB]
    apply(fastforce simp add: has_sup_def)
*)

  have BB_Bsup : "b = [^ b, b ^]"
    using sup_to_bsup[OF BB]
    by auto

  have Conc' : "b = [^ LUpd_Idem l1 s (LOut l1 s [^ LPost l1 s b, LPost l2 s b ^]) b, 
                        LUpd_Idem l2 s (LOut l2 s [^ LPost l1 s b, LPost l2 s b ^]) b ^]"
    using Bsup1 Eq2_1 Eq2_2 Eq1_1 Eq1_2 BB_Bsup
    by(auto)

  then show "b = LUpd_Idem (merge_l l1 l2) s (LOut (merge_l l1 l2) s b) b"
    using Eq1_1 Eq1_2
    by(auto simp add: merge_l_def Let_def)
qed

locale merge_l_valid = merge_l_valid_weak +
  l_ortho_strong +
  in1 : lifting_valid l1 S1 +
  in2 : lifting_valid l2 S2

sublocale merge_l_valid \<subseteq> out : lifting_valid "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s
  fix x y  :: "'b * 'e"
  fix b :: "'c"

  obtain x1 x2 where X: "x = (x1, x2)"
    by(cases x; auto)

  obtain y1 y2 where Y: "y = (y1, y2)"
    by(cases y; auto)

  have BB: "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain supy1 where Supy1 : "is_sup {LUpd l1 s y1 b, LUpd l2 s y2 b} supy1"
    using compat[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsupy1 : "[^ LUpd l1 s y1 b, LUpd l2 s y2 b ^] = supy1"
    using sup_to_bsup[OF Supy1] by auto

  have Out1y1 : "LOut l1 s supy1 = y1"
    using compat_get1[OF BB Supy1] by auto

  have Out2y1 : "LOut l2 s supy1 = y2"
    using compat_get2[OF BB Supy1] by auto

  obtain supx1 where Supx1 : "is_sup {LUpd l1 s x1 b, LUpd l2 s x2 b} supx1"
    using compat[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsupx1 : "[^ LUpd l1 s x1 b, LUpd l2 s x2 b ^] = supx1"
    using sup_to_bsup[OF Supx1]
    by auto

  have Out1x1 : "LOut l1 s supx1 = x1"
    using compat_get1[OF BB Supx1]
    by auto

  have Out2x1 : "LOut l2 s supx1 = x2"
    using compat_get2[OF BB Supx1]
    by auto

  obtain supy2 where Supy2 : "is_sup {LUpd_Idem l1 s y1 b, LUpd_Idem l2 s y2 b} supy2"
    using compat_idem[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsupy2 : "[^LUpd_Idem l1 s y1 b, LUpd_Idem l2 s y2 b^] = supy2"
    using sup_to_bsup[OF Supy2]
    by auto

  have Out1y2 : "LOut l1 s supy2 = y1"
    using compat_idem_get1[OF BB Supy2]
    by auto

  have Out2y2 : "LOut l2 s supy2 = y2"
    using compat_idem_get2[OF BB Supy2]
    by auto

  have Y2Y2 : "is_sup {supy2, supy2} supy2"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain supx1' where Supx1' :
    "is_sup {LUpd l1 s x1 supy2, LUpd l2 s x2 supy2} supx1'"
    using compat[OF Y2Y2]
    by(fastforce simp add: has_sup_def)

  have Bsupx1' :
    "[^ LUpd l1 s x1 supy2, LUpd l2 s x2 supy2 ^] = supx1'"
    using sup_to_bsup[OF Supx1']
    by auto

  have Out1x1' : "LOut l1 s supx1' = x1"
    using compat_get1[OF Y2Y2 Supx1']
    by auto

  have Out2x1' : "LOut l2 s supx1' = x2"
    using compat_get2[OF Y2Y2 Supx1']
    by auto

  have PutPut_1 : "LUpd_Idem l1 s x1 (LUpd_Idem l1 s y1 b) = LUpd_Idem l1 s x1 b"
    using in1.put_put by auto

  have PutPut_2 : "LUpd_Idem l2 s x2 (LUpd_Idem l2 s y2 b) = LUpd_Idem l2 s x2 b"
    using in2.put_put by auto 

  obtain supx1'_idem where Supx1'_Idem :
    "is_sup {LUpd_Idem l1 s x1 supy2, LUpd_Idem l2 s x2 supy2} supx1'_idem"
    using compat_idem[OF Y2Y2]
    by(fastforce simp add: has_sup_def)

  have Bsupx1'_Idem :
    "[^LUpd_Idem l1 s x1 supy2, LUpd_Idem l2 s x2 supy2^] = supx1'_idem"
    using sup_to_bsup[OF Supx1'_Idem]
    by auto

  obtain supx1_idem where Supx1_Idem :
    "is_sup {LUpd_Idem l1 s x1 b, LUpd_Idem l2 s x2 b} supx1_idem"
    using compat_idem[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsupx1_Idem :
    "[^ LUpd_Idem l1 s x1 b, LUpd_Idem l2 s x2 b^] = supx1_idem"
    using sup_to_bsup[OF Supx1_Idem]
    by auto

  have Eq : "supx1'_idem = supx1_idem"
    using compat_put_put[OF BB Supy2 Supx1'_Idem Supx1_Idem]
    by auto

  show "LUpd_Idem (merge_l l1 l2) s x (LUpd_Idem (merge_l l1 l2) s y b) = LUpd_Idem (merge_l l1 l2) s x b"
    using X Y 
    by(auto simp add: merge_l_def Let_def
      Bsupy1 Bsupx1 
      Out1x1 Out2x1
      Out1y1 Out2y1 Bsupy2
      Out1y2 Out2y2
      Bsupx1'
      Out1x1' Out2x1'
      Bsupx1_Idem Bsupx1'_Idem Eq
      simp del: LUpd_def)
qed

locale merge_l_valid_weak_base = merge_l_valid_weak + l_ortho_base +
  in1 : lifting_valid_base l1 S1 +
  in2 : lifting_valid_base l2 S2

sublocale merge_l_valid_weak_base \<subseteq> out : lifting_valid_weak_base "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s :: "'a"

  have Supr : "is_sup {LBase l1 s, LBase l2 s} (\<bottom> :: 'c)" 
    using compat_bases[of s] by auto

  have Eq : "[^ LBase l1 s, LBase l2 s ^] = \<bottom>"
    using is_sup_unique[OF bsup_sup[OF Supr bsup_spec] Supr] by simp

  show "LBase (merge_l l1 l2) s = \<bottom>" using Eq
    by(auto simp add: merge_l_def)
qed

locale merge_l_valid_base = merge_l_valid + merge_l_valid_weak_base

sublocale merge_l_valid_base \<subseteq> out : lifting_valid_base "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
qed

locale merge_l_valid_weak_ok = merge_l_valid_weak + l_ortho_ok +
  in1 : lifting_valid_weak_ok l1 S1 +
  in2 : lifting_valid_weak_ok l2 S2

sublocale merge_l_valid_weak_ok \<subseteq> out : lifting_valid_weak_ok "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s

  show "ok_S \<subseteq> S1 s \<inter> S2 s"
    using in1.ok_S_valid in2.ok_S_valid by auto
next
  fix s 
  fix a :: "'b * 'e"
  fix b :: "'c"

  assume B_ok : "b \<in> ok_S"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have BB: "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  then obtain supr where Supr : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr"
    using compat[OF BB, of s a1 a2]
    by(auto simp add: has_sup_def)

  have Bsupr : "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = supr"
    using is_sup_unique[OF bsup_sup[OF Supr bsup_spec] Supr] by simp

  have Out1: "LOut l1 s [^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = a1"
    using compat_get1[OF BB Supr] unfolding Bsupr
    by auto

  have Out2 : "LOut l2 s [^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = a2"
    using compat_get2[OF BB Supr] unfolding Bsupr
    by auto

  obtain supr' where Supr' : "is_sup {LUpd_Idem l1 s a1 b, LUpd_Idem l2 s a2 b} supr'"
    using compat_idem[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsupr' : "[^ LUpd_Idem l1 s a1 b, LUpd_Idem l2 s a2 b ^] = supr'"
    using is_sup_unique[OF bsup_sup[OF Supr' bsup_spec] Supr'] by simp

  show "LUpd_Idem (merge_l l1 l2) s a b
       \<in> ok_S"
    using compat_idem_ok[OF B_ok Supr'] Bsupr Bsupr' A Out1 Out2
    by(auto simp add: merge_l_def simp del: LUpd_def)
next

  fix s 
  fix b :: 'c

  assume B_ok : "b \<in> ok_S"

  have BB: "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain supr where Supr : "is_sup {LPost l1 s b, LPost l2 s b} supr"
    using compat_post[OF BB]
    by(fastforce simp add: has_sup_def)

  have Bsupr: "supr = [^ LPost l1 s b, LPost l2 s b^]"
    using sup_to_bsup[OF Supr]
    by auto

  show "LPost (merge_l l1 l2) s b \<in> ok_S"
    using compat_post_ok[OF B_ok Supr] Bsupr
    by(auto simp add: merge_l_def)
qed

locale merge_l_valid_ok = merge_l_valid_weak_ok + merge_l_valid

sublocale merge_l_valid_ok \<subseteq> out : lifting_valid_ok "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
qed

locale merge_l_valid_weak_base_ok = merge_l_valid_weak_ok + merge_l_valid_weak_base
sublocale merge_l_valid_weak_base_ok \<subseteq> out : lifting_valid_weak_base_ok "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
qed

locale merge_l_valid_base_ok = merge_l_valid_weak_base_ok + merge_l_valid_ok
sublocale merge_l_valid_base_ok \<subseteq> out : lifting_valid_base_ok "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
qed

(* Supr' could be ub *)
lemma sup_compare2 :
  assumes Supr : "is_sup {x, y} z"
  assumes Supr' : "is_sup {x', y'} z'"
  assumes Leq_x : "x <[ x'"
  assumes Leq_y : "y <[ y'"
  shows "z <[ z'"
proof-

  have "is_ub {x, y} z'"
  proof(rule is_ubI)
    fix w
    assume "w \<in> {x, y}"

    then consider (1) "w = x" | (2) "w = y"
      by auto
    then show "w <[ z'"
    proof cases
      case 1
      have Leq_x' : "x' <[ z'"
        using is_supD1[OF Supr', of x']
        by auto
      then show ?thesis 
        using leq_trans[OF Leq_x Leq_x'] 1
        by auto        
    next
      case 2
      have Leq_y' : "y' <[ z'"
        using is_supD1[OF Supr', of y']
        by auto
      then show ?thesis
        using leq_trans[OF Leq_y Leq_y'] 2
        by auto
    qed
  qed

  then show "z <[ z'"
    using is_supD2[OF Supr]
    by auto
qed

lemma sup_ub_compare2 :
  assumes Supr : "is_sup {x, y} z"
  assumes Ub : "is_ub {x', y'} z'"
  assumes Leq_x : "x <[ x'"
  assumes Leq_y : "y <[ y'"
  shows "z <[ z'"
proof-

  have "is_ub {x, y} z'"
  proof(rule is_ubI)
    fix w
    assume "w \<in> {x, y}"

    then consider (1) "w = x" | (2) "w = y"
      by auto
    then show "w <[ z'"
    proof cases
      case 1
      have Leq_x' : "x' <[ z'"
        using is_ubE[OF Ub, of x']
        by auto
      then show ?thesis 
        using leq_trans[OF Leq_x Leq_x'] 1
        by auto        
    next
      case 2
      have Leq_y' : "y' <[ z'"
        using is_ubE[OF Ub, of y']
        by auto
      then show ?thesis
        using leq_trans[OF Leq_y Leq_y'] 2
        by auto
    qed
  qed

  then show "z <[ z'"
    using is_supD2[OF Supr]
    by auto
qed


(*
locale merge_l_valid_weak_pres = merge_l_valid_weak +
  in1 : lifting_valid_weak_pres l1 S1 +
  in2 : lifting_valid_weak_pres l2 S2
*)

locale merge_l_valid_presonly =
  merge_l_valid_weak' +
  l_ortho +
  in1 : lifting_valid_weak_pres l1 S1 +
  in2 : lifting_valid_weak_pres l2 S2

sublocale merge_l_valid_presonly \<subseteq> out: lifting_presonly "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof

(* function component has type d * f  *)

  fix v supr :: 'c
  fix V
  fix f :: "'d * 'f"
  fix s :: 'a

  assume Vin : "v \<in> V"
  assume Vsub : "V \<subseteq> S1 s \<inter> S2 s"
  then have Vsub1 : "V \<subseteq> S1 s" and Vsub2 : "V \<subseteq> S2 s"
    by auto

  assume Supr : "is_sup V supr" 
  assume Supr_in : "supr \<in> S1 s \<inter> S2 s"

  then have Supr_in1 : "supr \<in> S1 s" and Supr_in2 : "supr \<in> S2 s"
    by auto

  obtain f1 f2 where F: "f = (f1, f2)"
    by(cases f; auto)

  have Pres1 : "is_sup (LMap_Idem l1 f1 s ` V) (LMap_Idem l1 f1 s supr)"
    using in1.pres[OF Vin Vsub1 Supr Supr_in1, of f1]
    by auto

  have Pres2 : "is_sup (LMap_Idem l2 f2 s ` V) (LMap_Idem l2 f2 s supr)"
    using in2.pres[OF Vin Vsub2 Supr Supr_in2, of f2]
    by auto

  have SupSup : "is_sup {supr, supr} supr"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain supr1 where Supr1 :
    "is_sup { (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s supr)) supr),
              (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s supr)) supr) } supr1"
    using compat_idem[OF SupSup]
    by(fastforce simp add: has_sup_def)

  have Bsupr1 :
    "[^ (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s supr)) supr),
              (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s supr)) supr) ^] = supr1"
    using sup_to_bsup[OF Supr1]
    by(auto)

  obtain supr2 where Supr2 :
    "is_sup { LPost l1 s (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s supr)) supr),
              LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s supr)) supr) } supr2"
    using compat_post[OF Supr1]
    by(fastforce simp add: has_sup_def)
      
  have Bsupr2 :
    "[^ LPost l1 s
               (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s supr))
                 supr), LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s supr)) supr) ^] = supr2"
    using sup_to_bsup[OF Supr2]
    by auto

  have Out1_1 : "LOut l1 s supr1 = LFD l1 f1 s (LOut l1 s supr)"
    using compat_idem_get1[OF SupSup Supr1]
    by auto
    
  have Out1_2: "LOut l1 s supr2 = LFD l1 f1 s (LOut l1 s supr)"
    using compat_post_get1[OF Supr1 Supr2] Out1_1
    by auto

  have Out2_1 : "LOut l2 s supr1 = LFD l2 f2 s (LOut l2 s supr)"
    using compat_idem_get2[OF SupSup Supr1]
    by auto

  have Out2_2 : "LOut l2 s supr2 = LFD l2 f2 s (LOut l2 s supr)"
    using compat_post_get2[OF Supr1 Supr2] Out2_1
    by auto

  obtain supr3 where Supr3 :
    "is_sup {LUpd_Idem l1 s (LOut l1 s supr2) supr, LUpd_Idem l2 s (LOut l2 s supr2) supr} supr3" 
    using compat_idem[OF SupSup]
    by(fastforce simp add: has_sup_def)

  have Bsupr3 : "[^ LUpd_Idem l1 s (LOut l1 s supr2) supr, LUpd_Idem l2 s (LOut l2 s supr2) supr^] = supr3"
    using sup_to_bsup[OF Supr3]
    by auto

  obtain supr4 where Supr4 :
    "is_sup {LUpd_Idem l1 s (LOut l1 s supr1) supr, LUpd_Idem l2 s (LOut l2 s supr1) supr} supr4" 
    using compat_idem[OF SupSup]
    by(fastforce simp add: has_sup_def)

  have Bsupr4 : "[^ LUpd_Idem l1 s (LOut l1 s supr1) supr, LUpd_Idem l2 s (LOut l2 s supr1) supr^] = supr4"
    using sup_to_bsup[OF Supr4]
    by auto

  have Pres1 :
    "is_sup (LMap_Idem l1 f1 s ` V) (LMap_Idem l1 f1 s supr)"
    using in1.pres[OF Vin Vsub1 Supr Supr_in1, of f1]
    by auto

  have Pres2 :
    "is_sup (LMap_Idem l2 f2 s ` V) (LMap_Idem l2 f2 s supr)"
    using in2.pres[OF Vin Vsub2 Supr Supr_in2, of f2]
    by auto


  show "is_sup (LMap_Idem (merge_l l1 l2) f s ` V) (LMap_Idem (merge_l l1 l2) f s supr)"
  proof(rule is_supI)
    fix xo

    assume Xo: "xo \<in> LMap_Idem (merge_l l1 l2) f s ` V"

    then obtain xi where Xi : "xi \<in> V" 
     "xo = LMap_Idem (merge_l l1 l2) f s xi"
      using F
      by auto

    have XiXi : "is_sup {xi, xi} xi"
      by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

    obtain suprxi_1 where Suprxi_1 :
      "is_sup { (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s xi)) xi),
                (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s xi)) xi) } suprxi_1"
      using compat_idem[OF XiXi]
      by(fastforce simp add: has_sup_def)
  
    have Bsuprxi_1 :
      "[^ (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s xi)) xi),
                (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s xi)) xi) ^] = suprxi_1"
      using sup_to_bsup[OF Suprxi_1]
      by(auto)
  
    obtain suprxi_2 where Suprxi_2 :
      "is_sup { LPost l1 s (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s xi)) xi),
                LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s xi)) xi) } suprxi_2"
      using compat_post[OF Suprxi_1]
      by(fastforce simp add: has_sup_def)
        
    have Bsuprxi_2 :
      "[^ LPost l1 s (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s xi)) xi),
                LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s xi)) xi) ^] = suprxi_2"
      using sup_to_bsup[OF Suprxi_2]
      by auto
  
    have Xi_Out1_1 : "LOut l1 s suprxi_1 = LFD l1 f1 s (LOut l1 s xi)"
      using compat_idem_get1[OF XiXi Suprxi_1]
      by auto
      
    have Xi_Out1_2: "LOut l1 s suprxi_2 = LFD l1 f1 s (LOut l1 s xi)"
      using compat_post_get1[OF Suprxi_1 Suprxi_2] Xi_Out1_1
      by auto
  
    have Xi_Out2_1 : "LOut l2 s suprxi_1 = LFD l2 f2 s (LOut l2 s xi)"
      using compat_idem_get2[OF XiXi Suprxi_1]
      by auto
  
    have Xi_Out2_2 : "LOut l2 s suprxi_2 = LFD l2 f2 s (LOut l2 s xi)"
      using compat_post_get2[OF Suprxi_1 Suprxi_2] Xi_Out2_1
      by auto

    have Leq1_1 : "LMap_Idem l1 f1 s xi <[ LMap_Idem l1 f1 s supr"
      using is_supD1[OF Pres1 imageI[OF Xi(1)]]
      by auto

    have Leq1_2 : "LMap_Idem l1 f1 s supr <[ supr1"
      using is_supD1[OF Supr1]
      by(auto)

    then have Leq1_3 : "LMap_Idem l1 f1 s xi <[ supr1"
      using leq_trans[OF Leq1_1 Leq1_2]
      by auto

    have Leq2_1 : "LMap_Idem l2 f2 s xi <[ LMap_Idem l2 f2 s supr"
      using is_supD1[OF Pres2 imageI[OF Xi(1)]]
      by auto

    have Leq2_2 : "LMap_Idem l2 f2 s supr <[ supr1"
      using is_supD1[OF Supr1]
      by(auto)

    then have Leq2_3 : "LMap_Idem l2 f2 s xi <[ supr1"
      using leq_trans[OF Leq2_1 Leq2_2]
      by auto

    have Leq_3_4 :
      "supr4 <[ supr3"
      using sup_compare2[OF Supr4 Supr3] Out1_1 Out2_1 Out1_2 Out2_2
      by (auto simp add: leq_refl)

    have Leq_Full : "suprxi_1 <[ supr4"
      using sup_compare2[OF Suprxi_1 Supr4]
        Leq1_1[unfolded LMap_Idem_def] Leq2_1[unfolded LMap_Idem_def]
        Out1_1 Out2_1
      by(auto)

    have Conc' : "suprxi_1 <[ supr3"
      using leq_trans[OF Leq_Full Leq_3_4]
      by auto

    then show "xo <[ LMap_Idem (merge_l l1 l2) f s supr"
      using F Xi
      by(auto simp add: merge_l_def Let_def Xi_Out1_2 Xi_Out2_2 Bsupr1 Bsupr2 Bsupr3
          Bsuprxi_1 Bsuprxi_2)
  next

    fix w

    assume Ub: "is_ub (LMap_Idem (merge_l l1 l2) f s ` V) w"

    have Ub1 : "is_ub (LMap_Idem l1 f1 s ` V) w"
    proof(rule is_ubI)
      fix k

      assume "k \<in> LMap_Idem l1 f1 s ` V"

      then obtain ko where Ko : "ko \<in> V" "LMap_Idem l1 f1 s ko = k"
        by auto

      then have W_Geq : "LMap_Idem (merge_l l1 l2) f s ko <[ w"
        using is_ubE[OF Ub imageI[OF Ko(1)]]
        by auto

      have KoKo : "is_sup {ko, ko} ko"
        by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)
  
      obtain suprko_1 where Suprko_1 :
        "is_sup { (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) } suprko_1"
        using compat_idem[OF KoKo]
        by(fastforce simp add: has_sup_def)
    
      have Bsuprko_1 :
        "[^ (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) ^] = suprko_1"
        using sup_to_bsup[OF Suprko_1]
        by(auto)
    
      obtain suprko_2 where Suprko_2 :
        "is_sup { LPost l1 s (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) } suprko_2"
        using compat_post[OF Suprko_1]
        by(fastforce simp add: has_sup_def)
          
      have Bsuprko_2 :
        "[^ LPost l1 s (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) ^] = suprko_2"
        using sup_to_bsup[OF Suprko_2]
        by auto
    
      have Ko_Out1_1 : "LOut l1 s suprko_1 = LFD l1 f1 s (LOut l1 s ko)"
        using compat_idem_get1[OF KoKo Suprko_1]
        by auto
        
      have Ko_Out1_2: "LOut l1 s suprko_2 = LFD l1 f1 s (LOut l1 s ko)"
        using compat_post_get1[OF Suprko_1 Suprko_2] Ko_Out1_1
        by auto
    
      have Ko_Out2_1 : "LOut l2 s suprko_1 = LFD l2 f2 s (LOut l2 s ko)"
        using compat_idem_get2[OF KoKo Suprko_1]
        by auto
    
      have Ko_Out2_2 : "LOut l2 s suprko_2 = LFD l2 f2 s (LOut l2 s ko)"
        using compat_post_get2[OF Suprko_1 Suprko_2] Ko_Out2_1
        by auto
  
      have Leq1_1 : "LMap_Idem l1 f1 s ko <[ LMap_Idem l1 f1 s supr"
        using is_supD1[OF Pres1 imageI[OF Ko(1)]]
        by auto
  
      have Leq1_2 : "LMap_Idem l1 f1 s supr <[ supr1"
        using is_supD1[OF Supr1]
        by(auto)
  
      then have Leq1_3 : "LMap_Idem l1 f1 s ko <[ supr1"
        using leq_trans[OF Leq1_1 Leq1_2]
        by auto
  
      have Leq2_1 : "LMap_Idem l2 f2 s ko <[ LMap_Idem l2 f2 s supr"
        using is_supD1[OF Pres2 imageI[OF Ko(1)]]
        by auto
  
      have Leq2_2 : "LMap_Idem l2 f2 s supr <[ supr1"
        using is_supD1[OF Supr1]
        by(auto)
  
      then have Leq2_3 : "LMap_Idem l2 f2 s ko <[ supr1"
        using leq_trans[OF Leq2_1 Leq2_2]
        by auto

      have Compare : "LMap_Idem l1 f1 s ko <[ LMap_Idem (merge_l l1 l2) f s ko"
        using F is_supD1[OF Suprko_1]
        by(simp add: merge_l_def Let_def Bsuprko_2 Bsuprko_1 Ko_Out1_2 Ko_Out2_2)

      then show "k <[ w"
        using leq_trans[OF Compare W_Geq] unfolding Ko
        by auto
    qed

    have Ub2 : "is_ub (LMap_Idem l2 f2 s ` V) w"
    proof(rule is_ubI)
      fix k

      assume "k \<in> LMap_Idem l2 f2 s ` V"

      then obtain ko where Ko : "ko \<in> V" "LMap_Idem l2 f2 s ko = k"
        by auto

      then have W_Geq : "LMap_Idem (merge_l l1 l2) f s ko <[ w"
        using is_ubE[OF Ub imageI[OF Ko(1)]]
        by auto

      have KoKo : "is_sup {ko, ko} ko"
        by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)
  
      obtain suprko_1 where Suprko_1 :
        "is_sup { (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) } suprko_1"
        using compat_idem[OF KoKo]
        by(fastforce simp add: has_sup_def)
    
      have Bsuprko_1 :
        "[^ (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) ^] = suprko_1"
        using sup_to_bsup[OF Suprko_1]
        by(auto)
    
      obtain suprko_2 where Suprko_2 :
        "is_sup { LPost l1 s (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) } suprko_2"
        using compat_post[OF Suprko_1]
        by(fastforce simp add: has_sup_def)
          
      have Bsuprko_2 :
        "[^ LPost l1 s (LUpd_Idem l1 s (LFD l1 f1 s (LOut l1 s ko)) ko),
                  LPost l2 s (LUpd_Idem l2 s (LFD l2 f2 s (LOut l2 s ko)) ko) ^] = suprko_2"
        using sup_to_bsup[OF Suprko_2]
        by auto
    
      have Ko_Out1_1 : "LOut l1 s suprko_1 = LFD l1 f1 s (LOut l1 s ko)"
        using compat_idem_get1[OF KoKo Suprko_1]
        by auto
        
      have Ko_Out1_2: "LOut l1 s suprko_2 = LFD l1 f1 s (LOut l1 s ko)"
        using compat_post_get1[OF Suprko_1 Suprko_2] Ko_Out1_1
        by auto
    
      have Ko_Out2_1 : "LOut l2 s suprko_1 = LFD l2 f2 s (LOut l2 s ko)"
        using compat_idem_get2[OF KoKo Suprko_1]
        by auto
    
      have Ko_Out2_2 : "LOut l2 s suprko_2 = LFD l2 f2 s (LOut l2 s ko)"
        using compat_post_get2[OF Suprko_1 Suprko_2] Ko_Out2_1
        by auto
  
      have Leq1_1 : "LMap_Idem l1 f1 s ko <[ LMap_Idem l1 f1 s supr"
        using is_supD1[OF Pres1 imageI[OF Ko(1)]]
        by auto
  
      have Leq1_2 : "LMap_Idem l1 f1 s supr <[ supr1"
        using is_supD1[OF Supr1]
        by(auto)
  
      then have Leq1_3 : "LMap_Idem l1 f1 s ko <[ supr1"
        using leq_trans[OF Leq1_1 Leq1_2]
        by auto
  
      have Leq2_1 : "LMap_Idem l2 f2 s ko <[ LMap_Idem l2 f2 s supr"
        using is_supD1[OF Pres2 imageI[OF Ko(1)]]
        by auto
  
      have Leq2_2 : "LMap_Idem l2 f2 s supr <[ supr1"
        using is_supD1[OF Supr1]
        by(auto)
  
      then have Leq2_3 : "LMap_Idem l2 f2 s ko <[ supr1"
        using leq_trans[OF Leq2_1 Leq2_2]
        by auto

      have Compare : "LMap_Idem l2 f2 s ko <[ LMap_Idem (merge_l l1 l2) f s ko"
        using F is_supD1[OF Suprko_1]
        by(simp add: merge_l_def Let_def Bsuprko_2 Bsuprko_1 Ko_Out1_2 Ko_Out2_2)

      then show "k <[ w"
        using leq_trans[OF Compare W_Geq] unfolding Ko
        by auto
    qed

    have Ub3 : "is_ub {LMap_Idem l1 f1 s supr, LMap_Idem l2 f2 s supr} w"
    proof
      fix k

      assume "k \<in> {LMap_Idem l1 f1 s supr, LMap_Idem l2 f2 s supr}"

      then show "k <[ w" using is_supD2[OF Pres1 Ub1] is_supD2[OF Pres2 Ub2]
        by auto
    qed

    have "[^ LMap_Idem l1 f1 s supr, LMap_Idem l2 f2 s supr ^] <[ w"
      using is_supD2[OF Supr1 Ub3[unfolded LMap_Idem_def]] Bsupr1
      by auto

    then have Leq_conc_1 : "supr1 <[ w"
      using Bsupr1 by auto

    have Leq_conc_2 : "supr3 <[ supr1"
      using sup_compare2[OF Supr3 Supr1] leq_refl
      by(auto simp add: Out1_2 Out2_2)

    have Leq_conc : "supr3 <[ w"
      using leq_trans[OF Leq_conc_2 Leq_conc_1]
      by auto

    then show "LMap_Idem (merge_l l1 l2) f s supr <[ w" using F 
      by(simp add: merge_l_def Let_def Bsupr1 Bsupr2 Bsupr3)
  qed
next
  fix v supr :: 'c
  fix V
  fix s :: 'a

  assume Vin : "v \<in> V"
  assume Vsub : "V \<subseteq> S1 s \<inter> S2 s"
  then have Vsub1 : "V \<subseteq> S1 s" and Vsub2 : "V \<subseteq> S2 s"
    by auto

  assume Supr : "is_sup V supr" 
  assume Supr_in : "supr \<in> S1 s \<inter> S2 s"

  then have Supr_in1 : "supr \<in> S1 s" and Supr_in2 : "supr \<in> S2 s"
    by auto

  have Pres1 : "is_sup (LPost l1 s ` V) (LPost l1 s supr)"
    using in1.pres_post[OF Vin Vsub1 Supr Supr_in1]
    by auto

  have Pres2 : "is_sup (LPost l2 s ` V) (LPost l2 s supr)"
    using in2.pres_post[OF Vin Vsub2 Supr Supr_in2]
    by auto

  have SupSup : "is_sup {supr, supr} supr"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  obtain supr1 where Supr1 :
    "is_sup { (LPost l1 s supr),
              (LPost l2 s supr) } supr1"
    using compat_post[OF SupSup]
    by(fastforce simp add: has_sup_def)

  have Bsupr1 :
    "[^ (LPost l1 s supr),
              (LPost l2 s supr) ^] = supr1"
    using sup_to_bsup[OF Supr1]
    by(auto)

  show "is_sup (LPost (merge_l l1 l2) s ` V) (LPost (merge_l l1 l2) s supr)"
  proof(rule is_supI)

    fix xo

    assume Xo : "xo \<in> LPost (merge_l l1 l2) s ` V"

    then obtain xi where Xi : "xi \<in> V" "LPost (merge_l l1 l2) s xi = xo"
      by auto

    have XiXi : "is_sup {xi, xi} xi"
      by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

    obtain suprxi_1 where Suprxi_1 :
      "is_sup { (LPost l1 s xi),
                (LPost l2 s xi) } suprxi_1"
      using compat_post[OF XiXi]
      by(fastforce simp add: has_sup_def)
  
    have Bsuprxi_1 :
      "[^ (LPost l1 s xi),
                (LPost l2 s xi)  ^] = suprxi_1"
      using sup_to_bsup[OF Suprxi_1]
      by(auto)
  
    have Xi_Out1_1 : "LOut l1 s suprxi_1 = LOut l1 s xi"
      using compat_post_get1[OF XiXi Suprxi_1]
      by auto
      
    have Xi_Out2_1 : "LOut l2 s suprxi_1 = (LOut l2 s xi)"
      using compat_post_get2[OF XiXi Suprxi_1]
      by auto
  
    have Leq1_1 : "LPost l1 s xi <[ LPost l1 s supr"
      using is_supD1[OF Pres1 imageI[OF Xi(1)]]
      by auto

    have Leq2_1 : "LPost l2 s xi <[ LPost l2 s supr"
      using is_supD1[OF Pres2 imageI[OF Xi(1)]]
      by auto

    have Leq_Full : "suprxi_1 <[ supr1"
      using sup_compare2[OF Suprxi_1 Supr1]
        Leq1_1[unfolded LMap_Idem_def] Leq2_1[unfolded LMap_Idem_def]
      by(auto)

    show "xo <[ LPost (merge_l l1 l2) s supr"
      using Leq_Full Bsupr1 Xi Bsuprxi_1
      by(auto simp add: merge_l_def)
  next
    fix w

    assume Ub: "is_ub (LPost (merge_l l1 l2) s ` V) w"

    have Ub1 : "is_ub (LPost l1 s ` V) w"
    proof(rule is_ubI)
      fix k

      assume K : "k \<in> LPost l1 s ` V"

      then obtain ko where Ko : "ko \<in> V" "LPost l1 s ko = k"
        by auto

      then have W_Geq : "LPost (merge_l l1 l2) s ko <[ w"
        using is_ubE[OF Ub imageI[OF Ko(1)]]
        by auto

      have KoKo : "is_sup {ko, ko} ko"
        by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)
  
      obtain suprko_1 where Suprko_1 :
        "is_sup { (LPost l1 s ko),
                  (LPost l2 s ko) } suprko_1"
        using compat_post[OF KoKo]
        by(fastforce simp add: has_sup_def)
    
      have Bsuprko_1 :
        "[^ (LPost l1 s ko),
                  (LPost l2 s ko) ^] = suprko_1"
        using sup_to_bsup[OF Suprko_1]
        by(auto)
    
      have Ko_Out1_1 : "LOut l1 s suprko_1 = (LOut l1 s ko)"
        using compat_post_get1[OF KoKo Suprko_1]
        by auto
        
      have Ko_Out2_1 : "LOut l2 s suprko_1 = (LOut l2 s ko)"
        using compat_post_get2[OF KoKo Suprko_1]
        by auto
    
      have Leq1_1 : "LPost l1 s ko <[ LPost l1 s supr"
        using is_supD1[OF Pres1 imageI[OF Ko(1)]]
        by auto
  
      have Leq2_1 : "LPost l2 s ko <[ LPost l2 s supr"
        using is_supD1[OF Pres2 imageI[OF Ko(1)]]
        by auto
  
      have Compare : "LPost l1 s ko <[ LPost (merge_l l1 l2) s ko"
        using is_supD1[OF Suprko_1]
        by(simp add: merge_l_def Let_def Bsuprko_1)

      then show "k <[ w"
        using leq_trans[OF Compare W_Geq] unfolding Ko
        by auto
    qed

    have Ub2 : "is_ub (LPost l2 s ` V) w"
    proof(rule is_ubI)
      fix k

      assume K : "k \<in> LPost l2 s ` V"

      then obtain ko where Ko : "ko \<in> V" "LPost l2 s ko = k"
        by auto

      then have W_Geq : "LPost (merge_l l1 l2) s ko <[ w"
        using is_ubE[OF Ub imageI[OF Ko(1)]]
        by auto

      have KoKo : "is_sup {ko, ko} ko"
        by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)
  
      obtain suprko_1 where Suprko_1 :
        "is_sup { (LPost l1 s ko),
                  (LPost l2 s ko) } suprko_1"
        using compat_post[OF KoKo]
        by(fastforce simp add: has_sup_def)
    
      have Bsuprko_1 :
        "[^ (LPost l1 s ko),
                  (LPost l2 s ko) ^] = suprko_1"
        using sup_to_bsup[OF Suprko_1]
        by(auto)
    
      have Ko_Out1_1 : "LOut l1 s suprko_1 = (LOut l1 s ko)"
        using compat_post_get1[OF KoKo Suprko_1]
        by auto
        
      have Ko_Out2_1 : "LOut l2 s suprko_1 = (LOut l2 s ko)"
        using compat_post_get2[OF KoKo Suprko_1]
        by auto
    
      have Leq1_1 : "LPost l1 s ko <[ LPost l1 s supr"
        using is_supD1[OF Pres1 imageI[OF Ko(1)]]
        by auto
  
      have Leq2_1 : "LPost l2 s ko <[ LPost l2 s supr"
        using is_supD1[OF Pres2 imageI[OF Ko(1)]]
        by auto
  
      have Compare : "LPost l2 s ko <[ LPost (merge_l l1 l2) s ko"
        using is_supD1[OF Suprko_1]
        by(simp add: merge_l_def Let_def Bsuprko_1)

      then show "k <[ w"
        using leq_trans[OF Compare W_Geq] unfolding Ko
        by auto
    qed

    have Ub3 : "is_ub {LPost l1 s supr, LPost l2 s supr} w"
    proof
      fix k

      assume "k \<in> {LPost l1 s supr, LPost l2 s supr}"

      then show "k <[ w" using is_supD2[OF Pres1 Ub1] is_supD2[OF Pres2 Ub2]
        by auto
    qed

    have "[^ LPost l1 s supr, LPost l2 s supr ^] <[ w"
      using is_supD2[OF Supr1 Ub3[unfolded LMap_Idem_def]] Bsupr1
      by auto

    then show "LPost (merge_l l1 l2) s supr <[ w" 
      by(simp add: merge_l_def Let_def Bsupr1)
  qed
qed

locale merge_l_valid_weak_pres =
  merge_l_valid_weak +
  merge_l_valid_presonly

sublocale merge_l_valid_weak_pres \<subseteq> out : lifting_valid_weak_pres "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
qed

locale option_l_ortho =
  l_ortho (*+
  in1 : option_l_valid_weak l1 S1 +
  in2 : option_l_valid_weak l2 S2 *)

sublocale option_l_ortho \<subseteq> out : l_ortho "option_l l1"  "option_l_S S1" "option_l l2" "option_l_S S2"
proof
  fix s
  show "LBase (option_l l1) s = LBase (option_l l2) s"
    by(auto simp add: option_l_def)
next

  fix s a1 a2 
  fix b1 b2 :: "'c option"
  fix supr

  show "has_sup {LUpd_Idem (option_l l1) s a1 b1, LUpd_Idem (option_l l2) s a2 b2}"
    apply(cases b1; simp; cases b2; simp add: option_l_def)

  assume Supr : "is_sup {b1, b2} supr"

  fix b s 
  fix a1 :: 'b
  fix a2 :: 'e

  have Base: "LBase l1 s = LBase l2 s"
    using eq_base by auto

  show "has_sup
        {LUpd (option_l l1) s a1 b,
         LUpd (option_l l2) s a2 b}"
  proof(cases b)
    case None

    obtain sup where Sup :"is_sup
     {LUpd l1 s a1 (LBase l1 s),
      LUpd l2 s a2 (LBase l2 s)} sup"
      using compat[of s a1 "LBase l1 s" a2] Base
      by(auto simp add: has_sup_def)

    then have Sup' : "is_sup {LUpd (option_l l1) s a1 b,
         LUpd (option_l l2) s a2 b} (Some sup)"
      using is_sup_Some[OF _ Sup] None
      by(auto simp add: option_l_def)

    then show ?thesis
      by(auto simp add: has_sup_def)
  next

    case (Some b')
    obtain sup where Sup :"is_sup
     {LUpd l1 s a1 b',
      LUpd l2 s a2 b'} sup"
      using compat[of s a1 "b'" a2] Base
      by(auto simp add: has_sup_def)

    then have Sup' : "is_sup {LUpd (option_l l1) s a1 b,
         LUpd (option_l l2) s a2 b} (Some sup)"
      using is_sup_Some[OF _ Sup] Some
      by(auto simp add: option_l_def)
    then show ?thesis
      by(auto simp add: has_sup_def)
  qed
next

  fix b s a1 a2 supr

  assume Supr : "is_sup {LUpd (option_l l1) s a1 b, LUpd (option_l l2) s a2 b} supr"

  show "supr \<in> option_l_S S1 s \<inter> option_l_S S2 s"
    sorry

(*
  fix b s
  fix x1 :: "'c option"
  fix x2 :: "'c option"
  fix supr
(* YOU ARE HERE *)
  assume Sup: "is_sup {x1, x2} supr"

  assume X1 : "x1 \<in> option_l_S S1 s"
  assume X2 : "x2 \<in> option_l_S S2 s"

  obtain x1' where X1' : "x1 = Some x1'" "x1' \<in> S1 s"
    using X1 by(cases x1; auto simp add: option_l_S_def)

  obtain x2' where X2' : "x2 = Some x2'" "x2' \<in> S2 s"
    using X2 by(cases x2; auto simp add: option_l_S_def)

  show "supr \<in> option_l_S S1 s \<inter> option_l_S S2 s"
  proof(cases supr)
    case None

    then have "x1 <[ None"
      using is_supD1[OF Sup, of "x1"] unfolding X1 None
      by auto

    then have False using X1' by(simp add: option_pleq)

    thus ?thesis ..
  next
    case (Some supr')

    have Sup_map : "is_sup (Some ` {x1', x2'}) (Some supr')"
      using Sup unfolding X1' X2' Some
      by auto

    hence Sup_inner : "is_sup {x1', x2'} supr'"
      using is_sup_Some'[OF _ Sup_map]
      by auto

    hence Supr'_in : "supr' \<in> S1 s \<inter> S2 s"
      using compat_S[OF X1'(2) X2'(2) Sup_inner] by auto

    then show ?thesis
      using Some
      by(auto simp add: option_l_S_def)

  qed
*)
next

  fix b s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

  assume Sup :
    "is_sup {LUpd (option_l l1) s a1 b, LUpd (option_l l2) s a2 b} supr"

  obtain r1 where R1: "LUpd (option_l l1) s a1 b = Some r1"
    by(cases b; auto simp add: option_l_def)

  obtain r2 where R2 : "LUpd (option_l l2) s a2 b = Some r2"
    by(cases b; auto simp add: option_l_def)

  show "LOut (option_l l1) s supr = a1"
  proof(cases supr)
    case None

    then have "Some r1 <[ None"
      using is_supD1[OF Sup] unfolding R1 None
      by auto

    then have False by(simp add: option_pleq)

    thus ?thesis ..
  next
    case (Some supr')

    have Sup_map : "is_sup (Some ` {r1, r2}) (Some supr')"
      using Sup unfolding R1 R2 Some
      by auto

    hence Sup_inner : "is_sup {r1, r2} supr'"
      using is_sup_Some'[OF _ Sup_map]
      by auto

    then show ?thesis
    proof(cases b)
      case None' : None

      have R1' : "LUpd l1 s a1 (LBase l1 s) = r1"
        using None' R1
        by(auto simp add: option_l_def)

      have R2' : "LUpd l2 s a2 (LBase l2 s) = r2"
        using None' R2
        by(auto simp add: option_l_def)

      have Bases : "LBase l1 s = LBase l2 s"
        using eq_base by auto

      then have Sup_inner' :
        "is_sup {LUpd l1 s a1 (LBase l1 s), LUpd l2 s a2 (LBase l1 s)} supr'"
        using Sup_inner R1' R2'
        by auto
      
      then have "LOut l1 s supr' = a1"
        using compat_get1[OF Sup_inner']
        by auto

      then show ?thesis using Some
        by(auto simp add: option_l_def)
    next
      case Some' : (Some b')

      have R1' : "LUpd l1 s a1 b' = r1"
        using Some' R1
        by(auto simp add: option_l_def)

      have R2' : "LUpd l2 s a2 b' = r2"
        using Some' R2
        by(auto simp add: option_l_def)

      then have Sup_inner' :
        "is_sup {LUpd l1 s a1 b', LUpd l2 s a2 b'} supr'"
        using Sup_inner R1' R2'
        by auto

      show ?thesis
        using compat_get1[OF Sup_inner'] Some
        by(auto simp add: option_l_def)
    qed
  qed
next

  fix b s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

  assume Sup :
    "is_sup {LUpd (option_l l1) s a1 b, LUpd (option_l l2) s a2 b} supr"

  obtain r1 where R1: "LUpd (option_l l1) s a1 b = Some r1"
    by(cases b; auto simp add: option_l_def)

  obtain r2 where R2 : "LUpd (option_l l2) s a2 b = Some r2"
    by(cases b; auto simp add: option_l_def)

  show "LOut (option_l l2) s supr = a2"
  proof(cases supr)
    case None

    then have "Some r1 <[ None"
      using is_supD1[OF Sup] unfolding R1 None
      by auto

    then have False by(simp add: option_pleq)

    thus ?thesis ..
  next
    case (Some supr')

    have Sup_map : "is_sup (Some ` {r1, r2}) (Some supr')"
      using Sup unfolding R1 R2 Some
      by auto

    hence Sup_inner : "is_sup {r1, r2} supr'"
      using is_sup_Some'[OF _ Sup_map]
      by auto

    then show ?thesis
    proof(cases b)
      case None' : None

      have R1' : "LUpd l1 s a1 (LBase l1 s) = r1"
        using None' R1
        by(auto simp add: option_l_def)

      have R2' : "LUpd l2 s a2 (LBase l2 s) = r2"
        using None' R2
        by(auto simp add: option_l_def)

      have Bases : "LBase l1 s = LBase l2 s"
        using eq_base by auto

      then have Sup_inner' :
        "is_sup {LUpd l1 s a1 (LBase l1 s), LUpd l2 s a2 (LBase l1 s)} supr'"
        using Sup_inner R1' R2'
        by auto
      
      then have "LOut l2 s supr' = a2"
        using compat_get2[OF Sup_inner']
        by auto

      then show ?thesis using Some
        by(auto simp add: option_l_def)
    next
      case Some' : (Some b')

      have R1' : "LUpd l1 s a1 b' = r1"
        using Some' R1
        by(auto simp add: option_l_def)

      have R2' : "LUpd l2 s a2 b' = r2"
        using Some' R2
        by(auto simp add: option_l_def)

      then have Sup_inner' :
        "is_sup {LUpd l1 s a1 b', LUpd l2 s a2 b'} supr'"
        using Sup_inner R1' R2'
        by auto

      show ?thesis
        using compat_get2[OF Sup_inner'] Some
        by(auto simp add: option_l_def)
    qed
  qed
next

  fix s a b

  assume "b \<in> option_l_S S2 s"

  then obtain b' where B' : "b = Some b'" "b' \<in> S2 s"
    by(cases b; auto simp add: option_l_S_def)

  then have "LUpd l1 s a b' \<in> S2 s"
    using put1_S2[OF B'(2)]
    by auto

  then show "LUpd (option_l l1) s a b \<in> option_l_S S2 s"
    using B'
    by(auto simp add: option_l_def option_l_S_def)
next
  fix s a b

  assume "b \<in> option_l_S S1 s"

  then obtain b' where B' : "b = Some b'" "b' \<in> S1 s"
    by(cases b; auto simp add: option_l_S_def)

  then have "LUpd l2 s a b' \<in> S1 s"
    using put2_S1[OF B'(2)]
    by auto

  then show "LUpd (option_l l2) s a b \<in> option_l_S S1 s"
    using B'
    by(auto simp add: option_l_def option_l_S_def)
next

  fix b s a1 a2 supr

  assume "is_sup {LUpd (option_l l1) s a1 b, LUpd (option_l l2) s a2 b} supr"
  show "\<exists>b'. LUpd (option_l l1) s a1 b' = supr"
    sorry
next
  show "\<And>b s a1 a2 supr.
       is_sup {LUpd (option_l l1) s a1 b, LUpd (option_l l2) s a2 b} supr \<Longrightarrow>
       \<exists>b'. LUpd (option_l l2) s a2 b' = supr"
    sorry
qed
(*
next

  fix s a1 a2 b supr

  assume Supr : 
"is_sup
        {LUpd (option_l l1) s a1 b,
         LUpd (option_l l2) s a2 b}
        supr"
  show "\<exists>b'. LUpd (option_l l1) s a1 b' =
            supr" sorry
(*
  show "
       is_sup
        {LUpd (option_l l1) s a1 b,
         LUpd (option_l l2) s a2 b}
        (LUpd (option_l l1) s a1
          (LUpd (option_l l2) s a2 b))"
  proof(cases b)
    case None

    have Base: "LBase l1 s = LBase l2 s"
      using eq_base by auto

    have Sup :"is_sup
     {LUpd l1 s a1 (LBase l1 s),
      LUpd l2 s a2 (LBase l2 s)} (LUpd l1 s a1 (LUpd l2 s a2 (LBase l1 s)))"
      using compat'1[of s a1 "LBase l1 s" a2] Base
      by(auto simp add: has_sup_def)


    then show ?thesis
      using is_sup_Some[OF _ Sup] None Base
      by(auto simp add: option_l_def)
  next

    case (Some b')

    have Sup :"is_sup
     {LUpd l1 s a1 b',
      LUpd l2 s a2 b'} (LUpd l1 s a1 (LUpd l2 s a2 b'))"
      using compat'1[of s a1 "b'" a2] Some
      by(auto )

    then show ?thesis
      using is_sup_Some[OF _ Sup] Some 
      by(auto simp add: option_l_def)
  qed
*)

next
  fix s a1 a2 b supr

  assume Supr : "is_sup
        {LUpd (option_l l1) s a1 b,
         LUpd (option_l l2) s a2 b}
        supr"

  show"
       \<exists>b'. LUpd (option_l l2) s a2 b' =
            supr"
    sorry
(*

  show "
       is_sup
        {LUpd (option_l l1) s a1 b,
         LUpd (option_l l2) s a2 b}
        (LUpd (option_l l2) s a2
          (LUpd (option_l l1) s a1 b))"
  proof(cases b)
    case None

    have Base: "LBase l1 s = LBase l2 s"
      using eq_base by auto

    have Sup :"is_sup
     {LUpd l1 s a1 (LBase l1 s),
      LUpd l2 s a2 (LBase l2 s)} (LUpd l2 s a2 (LUpd l1 s a1 (LBase l1 s)))"
      using compat'2[of s a1 "LBase l1 s" a2] Base
      by(auto simp add: has_sup_def)


    then show ?thesis
      using is_sup_Some[OF _ Sup] None Base
      by(auto simp add: option_l_def)
  next

    case (Some b')

    have Sup :"is_sup
     {LUpd l1 s a1 b',
      LUpd l2 s a2 b'} (LUpd l2 s a2 (LUpd l1 s a1 b'))"
      using compat'2[of s a1 "b'" a2] Some
      by(auto )

    then show ?thesis
      using is_sup_Some[OF _ Sup] Some 
      by(auto simp add: option_l_def)
  qed

next
*)

qed
*)
lemma sup_singleton :
  "is_sup {x} x"
  by(auto simp add: is_least_def is_ub_def is_sup_def leq_refl)

(* don't need l_ortho_base assumption here. *)
locale option_l_ortho_base = option_l_ortho + l_ortho_base'

sublocale option_l_ortho_base \<subseteq> out : l_ortho_base "option_l l1" "option_l_S S1" "option_l l2" "option_l_S S2"
proof
  fix s

  show "is_sup
          {LBase (option_l l1) s,
           LBase (option_l l2) s}
          \<bottom>"
    using sup_singleton[of "None"]
    by(auto simp add: option_l_def option_bot)
qed

locale option_l_ortho_ok =
  option_l_ortho + l_ortho_ok

sublocale option_l_ortho_ok \<subseteq> out : l_ortho_ok "option_l l1" "option_l_S S1" "option_l l2" "option_l_S S2"
proof

  fix s a1 a2 b supr

  assume H: "is_sup {LUpd (option_l l1) s a1 b, LUpd (option_l l2) s a2 b} supr"

  assume Bok : "b \<in> ok_S"
  obtain r1 where R1: "LUpd (option_l l1) s a1 b = Some r1"
    by(cases b; auto simp add: option_l_def)

  obtain r2 where R2 : "LUpd (option_l l2) s a2 b = Some r2"
    by(cases b; auto simp add: option_l_def)

  show "supr \<in> ok_S"
  proof(cases supr)
    case None

    then have "Some r1 <[ None"
      using is_supD1[OF H] unfolding R1 None
      by auto

    then have False by(simp add: option_pleq)

    thus ?thesis ..
  next
    case (Some supr')

    have Sup_map : "is_sup (Some ` {r1, r2}) (Some supr')"
      using H unfolding R1 R2 Some
      by auto

    hence Sup_inner : "is_sup {r1, r2} supr'"
      using is_sup_Some'[OF _ Sup_map]
      by auto

    show ?thesis
    proof(cases b)
      case None' : None

      then have False using Bok
        by(auto simp add:option_ok_S)
(*
      have R1' : "LUpd l1 s a1 (LBase l1 s) = r1"
        using None' R1
        by(auto simp add: option_l_def)

      have R2' : "LUpd l2 s a2 (LBase l2 s) = r2"
        using None' R2
        by(auto simp add: option_l_def)

      have Bases : "LBase l1 s = LBase l2 s"
        using eq_base by auto

      then have Sup_inner' :
        "is_sup {LUpd l1 s a1 (LBase l1 s), LUpd l2 s a2 (LBase l1 s)} supr'"
        using Sup_inner R1' R2'
        by auto
      
      then have "supr' \<in> ok_S"
        using compat_ok[OF Sup_inner']
        by auto
*)
      then show ?thesis using Some
        by(auto simp add: option_l_def option_ok_S)
    next
      case Some' : (Some b')

      then have B'ok : "b' \<in> ok_S"
        using Bok
        by(auto simp add: option_ok_S)

      have R1' : "LUpd l1 s a1 b' = r1"
        using Some' R1
        by(auto simp add: option_l_def)

      have R2' : "LUpd l2 s a2 b' = r2"
        using Some' R2
        by(auto simp add: option_l_def)

      then have Sup_inner' :
        "is_sup {LUpd l1 s a1 b', LUpd l2 s a2 b'} supr'"
        using Sup_inner R1' R2'
        by auto

      then have "supr' \<in> ok_S"
        using compat_ok[OF B'ok Sup_inner']
        by auto

      then show ?thesis using Some
        by(auto simp add: option_l_def option_ok_S)
    qed
  qed
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

  fix b :: "('c * 'g)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain sup1 where Sup1 :
    "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b1} sup1"
    using compat[of s a1 b1 a2]
    by(auto simp add: has_sup_def)

  have "is_sup {LUpd (fst_l l1) s a1 b, LUpd (fst_l l2) s a2 b} (sup1, b2)"
    using is_sup_fst[OF _ Sup1, of _ b2] B
    by(auto simp add: fst_l_def)

  then show "has_sup {LUpd (fst_l l1) s a1 b, LUpd (fst_l l2) s a2 b}"
    by(auto simp add: has_sup_def)
next

  fix b supr :: "('c * 'g)"
  fix a1 a2
  fix s

  assume "is_sup
        {LUpd (fst_l l1) s a1 b,
         LUpd (fst_l l2) s a2 b}
        supr"
  show " supr \<in> fst_l_S S1 s \<inter> fst_l_S S2 s"
    sorry
(*
  then obtain x1 x2 where X: "x = (x1, x2)" "x1 \<in> S1 s"
    by(cases x; auto simp add: fst_l_S_def)

  assume "y \<in> fst_l_S S2 s"
  then obtain y1 y2 where Y: "y = (y1, y2)" "y1 \<in> S2 s"
    by(cases y; auto simp add: fst_l_S_def)

  assume Sup : "is_sup {x, y} supr"

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  have Sup' : "is_sup {x1, y1} s1"
    using X Y S
    is_sup_fst'[OF _ Sup[unfolded S]]
    by(auto simp add: fst_l_def)

  show "supr \<in> fst_l_S S1 s \<inter> fst_l_S S2 s"
    using compat_S[OF X(2) Y(2) Sup'] S
    by(auto simp add: fst_l_S_def)
*)
next

  fix b :: "('c * 'g)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr :: "('c * 'g)"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  assume Sup: "is_sup {LUpd (fst_l l1) s a1 b, LUpd (fst_l l2) s a2 b} supr"

  have Sup' : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b1} s1"
    using B S
    is_sup_fst'[OF _ Sup[unfolded S]]
    by(auto simp add: fst_l_def)

  show "LOut (fst_l l1) s supr = a1"
    using compat_get1[OF Sup'] S
    by(auto simp add: fst_l_def)
next

  fix b :: "('c * 'g)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr :: "('c * 'g)"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  assume Sup: "is_sup {LUpd (fst_l l1) s a1 b, LUpd (fst_l l2) s a2 b} supr"

  have Sup' : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b1} s1"
    using B S
    is_sup_fst'[OF _ Sup[unfolded S]]
    by(auto simp add: fst_l_def)

  show "LOut (fst_l l2) s supr = a2"
    using compat_get2[OF Sup'] S
    by(auto simp add: fst_l_def)

next

  fix s a b

  assume In: "b \<in> fst_l_S S2 s" 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then have "b1 \<in> S2 s" using In
    by(auto simp add: fst_l_S_def)

  then have "LUpd l1 s a b1 \<in> S2 s"
    using put1_S2 by auto

  then show "LUpd (fst_l l1) s a b \<in> fst_l_S S2 s"
    using B
    by(auto simp add: fst_l_def fst_l_S_def)

next

  fix s a b

  assume In: "b \<in> fst_l_S S1 s" 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then have "b1 \<in> S1 s" using In
    by(auto simp add: fst_l_S_def)

  then have "LUpd l2 s a b1 \<in> S1 s"
    using put2_S1 by auto

  then show "LUpd (fst_l l2) s a b \<in> fst_l_S S1 s"
    using B
    by(auto simp add: fst_l_def fst_l_S_def)

qed
(*
next

  fix b :: "('c * 'g)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  assume Sup : "is_sup
        {LUpd (fst_l l1) s a1 b,
         LUpd (fst_l l2) s a2 b}
        supr"

  obtain supr1 supr2 where Sup1_2 :
    "supr = (supr1, supr2)"
    by(cases supr; auto)

  have Sup1 : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b1} supr1"
    using is_sup_fst'[OF _ Sup[unfolded Sup1_2]] B
    by(auto simp add: fst_l_def)

  obtain b'1 where B'1 : "LUpd l1 s a1 b'1 = supr1" using compat'1[OF Sup1]
    by auto

  then have "LUpd (fst_l l1) s a1 (b'1, supr2) = supr"
    using Sup1_2 B
    by(auto simp add: fst_l_def)

  then show "\<exists>b'. LUpd (fst_l l1) s a1 b' = supr"
    by auto

next
  fix b :: "('c * 'g)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  assume Sup : "is_sup
        {LUpd (fst_l l1) s a1 b,
         LUpd (fst_l l2) s a2 b}
        supr"

  obtain supr1 supr2 where Sup1_2 :
    "supr = (supr1, supr2)"
    by(cases supr; auto)

  have Sup1 : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b1} supr1"
    using is_sup_fst'[OF _ Sup[unfolded Sup1_2]] B
    by(auto simp add: fst_l_def)


  obtain b'2 where B'2 : "LUpd l2 s a2 b'2 = supr1"
    using compat'2[OF Sup1]
    by auto

  then have "LUpd (fst_l l2) s a2 (b'2, supr2) = supr"
    using Sup1_2 B
    by(auto simp add: fst_l_def)

  then show "\<exists>b'. LUpd (fst_l l2) s a2 b' = supr"
    by auto
qed
*)
locale fst_l_ortho_base = fst_l_ortho + l_ortho_base

sublocale fst_l_ortho_base \<subseteq> out : l_ortho_base "fst_l l1" "fst_l_S S1" "fst_l l2" "fst_l_S S2"
proof
  fix s

  have Sup: "is_sup {LBase l1 s, LBase l2 s} \<bottom>"
    using compat_bases by auto

  then show "is_sup
          {LBase (fst_l l1) s,
           LBase (fst_l l2) s}
          \<bottom>"
    using is_sup_fst[OF _ Sup, of "LBase l1 s" \<bottom>]
    by(auto simp add: fst_l_def prod_bot)
qed

locale fst_l_ortho_ok = fst_l_ortho + l_ortho_ok

sublocale fst_l_ortho_ok \<subseteq> out : l_ortho_ok "fst_l l1" "fst_l_S S1" "fst_l l2" "fst_l_S S2"
proof
  fix b :: "('c * 'g)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr :: "('c * 'g)"

  assume Sup : "is_sup {LUpd (fst_l l1) s a1 b, LUpd (fst_l l2) s a2 b} supr"

  assume Bok : "b \<in> ok_S"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have B1ok : "b1 \<in> ok_S" and B2ok : "b2 \<in> ok_S"
    using Bok B by(auto simp add: prod_ok_S)

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  have Sup' : "is_sup {LUpd l1 s a1 b1, LUpd l2 s a2 b1} s1"
    using B S
    is_sup_fst'[OF _ Sup[unfolded S]]
    by(auto simp add: fst_l_def)

  have "s1 \<in> ok_S"
    using compat_ok[OF B1ok Sup'] by auto

  have SB2 : "is_sup {b2, b2} b2"
    using sup_singleton[of b2]
    by auto

  then have SS2:  "is_sup {b2, b2} s2" 
    using is_sup_snd'[OF _ Sup[unfolded S]] B
    by(auto simp add: fst_l_def)

(* need actual pord here. or do we? *)
  then have "b2 = s2"
    using is_sup_unique[of "{b2, b2}"]
    using is_sup_unique[OF `is_sup {b2, b2} b2`]
    by auto

  then have "s2 \<in> ok_S"
    using B2ok by auto

  show "supr \<in> ok_S"
    using `s1 \<in> ok_S` `s2 \<in> ok_S` S
    by(auto simp add: prod_ok_S)
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
  fix b :: "('g * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain sup2 where Sup2 :
    "is_sup {LUpd l1 s a1 b2, LUpd l2 s a2 b2} sup2"
    using compat[of s a1 b2 a2]
    by(auto simp add: has_sup_def)

  have "is_sup {LUpd (snd_l l1) s a1 b, LUpd (snd_l l2) s a2 b} (b1, sup2)"
    using is_sup_snd[OF _ Sup2, of _ b1] B
    by(auto simp add: snd_l_def)

  then show "has_sup {LUpd (snd_l l1) s a1 b, LUpd (snd_l l2) s a2 b}"
    by(auto simp add: has_sup_def)
next

  fix b supr :: "('g * 'c)"
  fix s a1 a2

  assume "is_sup
        {LUpd (snd_l l1) s a1 b,
         LUpd (snd_l l2) s a2 b}
        supr"
(*
  then obtain x1 x2 where X: "x = (x1, x2)" "x2 \<in> S1 s"
    by(cases x; auto simp add: snd_l_S_def)

  assume "y \<in> snd_l_S S2 s"
  then obtain y1 y2 where Y: "y = (y1, y2)" "y2 \<in> S2 s"
    by(cases y; auto simp add: snd_l_S_def)

  assume Sup : "is_sup {x, y} supr"

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  have Sup' : "is_sup {x2, y2} s2"
    using X Y S
    is_sup_snd'[OF _ Sup[unfolded S]]
    by(auto)
*)

  show "supr \<in> snd_l_S S1 s \<inter> snd_l_S S2 s"
    sorry
(*
    using compat_S[OF X(2) Y(2) Sup'] S
    by(auto simp add: snd_l_S_def)
*)
next

  fix b :: "('g * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr :: "('g * 'c)"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  assume Sup: "is_sup {LUpd (snd_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr"

  have Sup' : "is_sup {LUpd l1 s a1 b2, LUpd l2 s a2 b2} s2"
    using B S
    is_sup_snd'[OF _ Sup[unfolded S]]
    by(auto simp add: snd_l_def)

  show "LOut (snd_l l1) s supr = a1"
    using compat_get1[OF Sup'] S
    by(auto simp add: snd_l_def)
next

  fix b :: "('g * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr :: "('g * 'c)"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  assume Sup: "is_sup {LUpd (snd_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr"

  have Sup' : "is_sup {LUpd l1 s a1 b2, LUpd l2 s a2 b2} s2"
    using B S
    is_sup_snd'[OF _ Sup[unfolded S]]
    by(auto simp add: snd_l_def)

  show "LOut (snd_l l2) s supr = a2"
    using compat_get2[OF Sup'] S
    by(auto simp add: snd_l_def)

next

  fix s a b

  assume In: "b \<in> snd_l_S S2 s" 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then have "b2 \<in> S2 s" using In
    by(auto simp add: snd_l_S_def)

  then have "LUpd l1 s a b2 \<in> S2 s"
    using put1_S2 by auto

  then show "LUpd (snd_l l1) s a b \<in> snd_l_S S2 s"
    using B
    by(auto simp add: snd_l_def snd_l_S_def)

next

  fix s a b

  assume In: "b \<in> snd_l_S S1 s" 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then have "b2 \<in> S1 s" using In
    by(auto simp add: snd_l_S_def)

  then have "LUpd l2 s a b2 \<in> S1 s"
    using put2_S1 by auto

  then show "LUpd (snd_l l2) s a b \<in> snd_l_S S1 s"
    using B
    by(auto simp add: snd_l_def snd_l_S_def)

qed
(*
next

  fix b :: "('g * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  assume Sup : "is_sup {LUpd (snd_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr"

  obtain supr1 supr2 where Sup1_2 :
    "supr = (supr1, supr2)"
    by(cases supr; auto)

  have Sup2 : "is_sup {LUpd l1 s a1 b2, LUpd l2 s a2 b2} supr2"
    using is_sup_snd'[OF _ Sup[unfolded Sup1_2]] B
    by(auto simp add: snd_l_def)

  obtain b'1 where B'1 : "LUpd l1 s a1 b'1 = supr2" using compat'1[OF Sup2]
    by auto

  then have "LUpd (snd_l l1) s a1 (supr1, b'1) = supr"
    using Sup1_2 B
    by(auto simp add: snd_l_def)

  then show "\<exists>b'. LUpd (snd_l l1) s a1 b' = supr"
    by auto

next
  fix b :: "('g * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr 

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  assume Sup : "is_sup {LUpd (snd_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr"

  obtain supr1 supr2 where Sup1_2 :
    "supr = (supr1, supr2)"
    by(cases supr; auto)

  have Sup2 : "is_sup {LUpd l1 s a1 b2, LUpd l2 s a2 b2} supr2"
    using is_sup_snd'[OF _ Sup[unfolded Sup1_2]] B
    by(auto simp add: snd_l_def)

  obtain b'2 where B'2 : "LUpd l2 s a2 b'2 = supr2" using compat'2[OF Sup2]
    by auto

  then have "LUpd (snd_l l2) s a2 (supr1, b'2) = supr"
    using Sup1_2 B
    by(auto simp add: snd_l_def)

  then show "\<exists>b'. LUpd (snd_l l2) s a2 b' = supr"
    by auto

qed
*)
locale snd_l_ortho_base = snd_l_ortho + l_ortho_base

sublocale snd_l_ortho_base \<subseteq> out : l_ortho_base "snd_l l1" "snd_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s

  have Sup: "is_sup {LBase l1 s, LBase l2 s} \<bottom>"
    using compat_bases by auto

  then show "is_sup
          {LBase (snd_l l1) s,
           LBase (snd_l l2) s}
          \<bottom>"
    using is_sup_snd[OF _ Sup, of "LBase l1 s" \<bottom>]
    by(auto simp add: snd_l_def prod_bot)
qed

locale snd_l_ortho_ok = snd_l_ortho + l_ortho_ok

sublocale snd_l_ortho_ok \<subseteq> out : l_ortho_ok "snd_l l1" "snd_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix b :: "('g * 'c)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr :: "('g * 'c)"

  assume Sup : "is_sup {LUpd (snd_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr"

  assume Bok : "b \<in> ok_S"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  have B1ok : "b1 \<in> ok_S" and B2ok : "b2 \<in> ok_S"
    using Bok B by(auto simp add: prod_ok_S)

  obtain s1 s2 where S: "supr = (s1, s2)"
    by(cases supr; auto)

  have Sup' : "is_sup {LUpd l1 s a1 b2, LUpd l2 s a2 b2} s2"
    using B S
    is_sup_snd'[OF _ Sup[unfolded S]]
    by(auto simp add: snd_l_def)

  have "s2 \<in> ok_S"
    using compat_ok[OF B2ok Sup'] by auto

  have SB2 : "is_sup {b1, b1} b1"
    using sup_singleton[of b1]
    by auto

  then have SS2:  "is_sup {b1, b1} s1" 
    using is_sup_fst'[OF _ Sup[unfolded S]] B
    by(auto simp add: snd_l_def)

(* need actual pord here. or do we? *)
  then have "b1 = s1"
    using is_sup_unique[of "{b1, b1}"]
    using is_sup_unique[OF `is_sup {b1, b1} b1`]
    by auto

  then have "s1 \<in> ok_S"
    using B1ok by auto

  show "supr \<in> ok_S"
    using `s1 \<in> ok_S` `s2 \<in> ok_S` S
    by(auto simp add: prod_ok_S)
qed

locale fst_l_snd_l_ortho' =
  fixes l1 :: "('a, 'b1, 'c1 :: Pordb, 'f1) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c1 set"
  fixes l2 :: "('a, 'b2, 'c2 :: Pordb, 'f2) lifting"
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

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'e

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)


  have "is_sup {LUpd (fst_l l1) s a1 b,
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
    
  then show "has_sup
        {LUpd (fst_l l1) s a1 b,
         LUpd (snd_l l2) s a2 b}"
    by(auto simp add: has_sup_def)

next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 a2
  fix supr

  assume Supr : "is_sup {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr"

  obtain supr1 supr2 where Supr1_2 : "supr = (supr1, supr2)"
    by(cases supr; auto)

  obtain b1 b2 where B : "b = (b1, b2)"
    by(cases b; auto)

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
    using is_sup_unique[OF Supr Sup']
    by auto
    
(* use is_sup_unique here to show that it is the two components. *)
  have Conc1 : "supr1 \<in> S1 s"
    using Supr1_2 Sup_eq
    in1.put_S
    by(auto)

  have Conc2 : "supr2 \<in> S2 s"
    using Supr1_2 Sup_eq
    in2.put_S
    by auto

  show "supr
       \<in> fst_l_S S1 s \<inter>
          snd_l_S S2 s"
    using Conc1 Conc2 Supr1_2
    by(auto simp add: fst_l_S_def snd_l_S_def)
next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

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

  show "LOut (fst_l l1) s supr = a1"
    using Sup_eq in1.put_get
    by(auto simp add: fst_l_def)

next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

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

  show "LOut (snd_l l2) s supr = a2"
    using Sup_eq in2.put_get
    by(auto simp add: snd_l_def)

next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a :: 'b

  assume Bin : "b \<in> snd_l_S S2 s"

  then show "LUpd (fst_l l1) s a b \<in> snd_l_S S2 s"
    by(auto simp add: fst_l_def snd_l_S_def)

next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a :: 'e

  assume Bin : "b \<in> fst_l_S S1 s"

  then show "LUpd (snd_l l2) s a b \<in> fst_l_S S1 s"
    by(auto simp add: fst_l_S_def snd_l_def)

qed
(*
next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  assume Sup: "is_sup {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr "

  obtain supr1 supr2 where Sup1_2 :
    "supr = (supr1, supr2)"
    by(cases supr; auto)


  have Sup': "is_sup
        {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b}
        (LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b))"
  proof(rule is_supI)
    fix x

    assume X: "x \<in> {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b}"

    then consider (X1) "x = LUpd (fst_l l1) s a1 b" |
                  (X2) "x = LUpd (snd_l l2) s a2 b"
      by auto

    then show "x <[ LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b)"
    proof cases
      case X1
      then show ?thesis using B leq_refl in2.get_put
        by(auto simp add: fst_l_def snd_l_def prod_pleq)
    next
      case X2
      then show ?thesis using B leq_refl in1.get_put
        by(auto simp add: fst_l_def snd_l_def prod_pleq)
    qed
  next

    fix x'
    assume Ub : "is_ub {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b} x'"

    obtain x'1 x'2 where X': "x' = (x'1, x'2)"
      by(cases x'; auto)

    have Up1 : "LUpd l1 s a1 b1 <[ x'1" and Up2 : "LUpd l2 s a2 b2 <[ x'2"
      using X' B is_ubE[OF Ub]
      by(auto simp add: fst_l_def snd_l_def prod_pleq)

    then show "LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b) <[ x'"
      using X' B
      by(auto simp add: fst_l_def snd_l_def prod_pleq)
  qed

  hence "supr = (LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b))"
    using is_sup_unique[OF Sup Sup'] by auto

  then show "\<exists>b'. LUpd (fst_l l1) s a1 b' = supr"
    by blast
next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  assume Sup: "is_sup {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b} supr "

  obtain supr1 supr2 where Sup1_2 :
    "supr = (supr1, supr2)"
    by(cases supr; auto)


  have Sup': "is_sup
        {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b}
        (LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b))"
  proof(rule is_supI)
    fix x

    assume X: "x \<in> {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b}"

    then consider (X1) "x = LUpd (fst_l l1) s a1 b" |
                  (X2) "x = LUpd (snd_l l2) s a2 b"
      by auto

    then show "x <[ LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    proof cases
      case X1
      then show ?thesis using B leq_refl in2.get_put
        by(auto simp add: fst_l_def snd_l_def prod_pleq)
    next
      case X2
      then show ?thesis using B leq_refl in1.get_put
        by(auto simp add: fst_l_def snd_l_def prod_pleq)
    qed
  next

    fix x'
    assume Ub : "is_ub {LUpd (fst_l l1) s a1 b, LUpd (snd_l l2) s a2 b} x'"

    obtain x'1 x'2 where X': "x' = (x'1, x'2)"
      by(cases x'; auto)

    have Up1 : "LUpd l1 s a1 b1 <[ x'1" and Up2 : "LUpd l2 s a2 b2 <[ x'2"
      using X' B is_ubE[OF Ub]
      by(auto simp add: fst_l_def snd_l_def prod_pleq)

    then show "LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b) <[ x'"
      using X' B
      by(auto simp add: fst_l_def snd_l_def prod_pleq)
  qed

  hence "supr = (LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b))"
    using is_sup_unique[OF Sup Sup'] by auto

  then show "\<exists>b'. LUpd (snd_l l2) s a2 b' = supr"
    by blast
qed
*)
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

locale fst_l_snd_l_ortho_base =
  fst_l_snd_l_ortho + 
  in1 : lifting_valid_weak_base l1 S1 +
  in2 : lifting_valid_weak_base l2 S2

sublocale fst_l_snd_l_ortho_base \<subseteq> out : l_ortho_base "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof
  fix s

  have "is_sup {(\<bottom>, \<bottom>)} (\<bottom>, \<bottom>)"
    using sup_singleton
    by(auto)

  then show "is_sup
          {LBase (fst_l l1) s,
           LBase (snd_l l2) s}
          \<bottom>"
    using in1.base in2.base
    by(auto simp add: fst_l_def snd_l_def prod_bot)
qed

locale merge_l_ortho' =
  fixes l1 :: "('a, 'b1, 'c :: {Mergeableb, Pordps}, 'f1) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c1 set"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c2 set"
  fixes l3 :: "('a, 'b3, 'c, 'f3) lifting"
  fixes S3 :: "'a \<Rightarrow> 'c3 set"

locale merge_l_ortho = merge_l_ortho' +
  orth1_2 : l_ortho l1 S1 l2 S2 + 
  orth1_3 : l_ortho l1 S1 l3 S3 +
  orth2_3 : l_ortho l2 S2 l3 S3 
  (* + valid3 : lifting_valid_weak_pres l3 S3*)

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
  fix a1_2 :: "'b * 'e"
  fix a3 :: 'g
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  obtain supr12 where Sup12 : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr12"
    using orth1_2.compat
    by(fastforce simp add: has_sup_def)

  then have Bsup12 : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} [^ LUpd l1 s a1 b, LUpd l2 s a2 b ^]"
    using bsup_sup[OF Sup12 bsup_spec]
    by auto

  have Eq12 : "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = supr12"
    using is_sup_unique[OF Sup12 Bsup12]
    by auto

  obtain sup_full where Full1 :
    "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b, LUpd l3 s a3 b} sup_full"
    using pairwise_sup[OF orth1_2.compat orth2_3.compat orth1_3.compat, of s a1 b a2 a3]
    by(auto simp add: has_sup_def)

  have Un : "({LUpd l1 s a1 b, LUpd l2 s a2 b} \<union> {LUpd l3 s a3 b}) = {LUpd l1 s a1 b, LUpd l2 s a2 b, LUpd l3 s a3 b}"
    by blast

  have "is_sup {[^ LUpd l1 s a1 b, LUpd l2 s a2 b^], LUpd l3 s a3 b} sup_full"
    using sup_union2[OF Bsup12 sup_singleton[of "LUpd l3 s a3 b"], of sup_full] Full1
    unfolding Un
    by(auto)
    
  then show "has_sup {LUpd (merge_l l1 l2) s a1_2 b, LUpd l3 s a3 b}"
    using A1_2
    by(auto simp add: merge_l_def has_sup_def)
next
  fix b supr :: 'c
  fix a1_2 :: "'b * 'e"
  fix a3 :: 'g
  fix s

  assume Supr : 
    "is_sup {LUpd (merge_l l1 l2) s a1_2 b, LUpd l3 s a3 b} supr"

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  obtain supr12 where Sup12 : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr12"
    using orth1_2.compat
    by(fastforce simp add: has_sup_def)

  have "supr12 \<in> (S1 s \<inter> S2 s)"
    using orth1_2.compat_S[OF Sup12]
    by auto

  obtain supr13 where Sup13 : "is_sup {LUpd l1 s a1 b, LUpd l3 s a3 b} supr13"
    using orth1_3.compat
    by(fastforce simp add: has_sup_def)

  have "supr13 \<in> (S1 s \<inter> S3 s)"
    using orth1_3.compat_S[OF Sup13]
    by auto

  obtain supr23 where Sup23 : "is_sup {LUpd l2 s a2 b, LUpd l3 s a3 b} supr23"
    using orth2_3.compat
    by(fastforce simp add: has_sup_def)

  have "supr23 \<in> (S2 s \<inter> S3 s)"
    using orth2_3.compat_S[OF Sup23]
    by auto

  have "has_sup {LUpd l1 s a1 b, LUpd l2 s a2 b, LUpd l3 s a3 b}"
    using pairwise_sup[OF orth1_2.compat orth2_3.compat orth1_3.compat]
    by fastforce



  then obtain supr' where Supr' : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b, LUpd l3 s a3 b} supr'"
    by(auto simp add: has_sup_def)

  obtain supr12_sub2 where Supr12_sub2 : "LUpd l1 s a1 supr12_sub2 = supr12" "supr12_sub2 \<in> S2 s"
    using orth1_2.compat'1[OF Sup12] by auto

  obtain supr12_sub1 where Supr12_sub1 : "LUpd l2 s a2 supr12_sub1 = supr12" "supr12_sub1 \<in> S1 s"
    using orth1_2.compat'2[OF Sup12] by auto

  obtain foo where Foo : "is_sup {LUpd l1 s a1 supr12_sub2, LUpd l3 s a3 supr12_sub2} foo"
    using orth1_3.compat by(fastforce simp add: has_sup_def)

  then have Foo' : "is_sup {LUpd l1 s a1 supr12_sub2, LUpd l3 s a3 supr12_sub2} foo"

  obtain mini where Mini : "LUpd l3 s a3 mini = foo" "mini \<in> S1 s"
    using orth1_3.compat'2[OF Foo]
    by auto

  obtain supr13_sub3 where Supr13_sub3 : "LUpd l1 s a1 supr13_sub3 = supr13" "supr13_sub3 \<in> S3 s"
    using orth1_3.compat'1[OF Sup13]
    by auto

  obtain supr13_sub1 where Supr13_sub2 : "LUpd l3 s a3 supr13_sub1 = supr13" "supr13_sub1 \<in> S1 s"
    using orth1_3.compat'2[OF Sup13]
    by auto

  obtain supr23_sub3 where Supr23_sub3 : "LUpd l2 s a2 supr23_sub3 = supr23" "supr23_sub3 \<in> S3 s"
    using orth2_3.compat'1[OF Sup23] by auto

  obtain supr23_sub2 where Supr23_sub2 : "LUpd l3 s a3 supr23_sub2 = supr23" "supr23_sub2 \<in> S2 s"
    using orth2_3.compat'2[OF Sup23] by auto



  show "supr \<in> S1 s \<inter> S2 s \<inter> S3 s"
    using pairwise_sup
    using Supr orth1_2.compat_S
    unfolding A1_2
    apply(simp add: merge_l_def)

end