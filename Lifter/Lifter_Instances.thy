theory Lifter_Instances imports Lifter
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
  LMake (\<lambda> s a a' . a) (\<lambda> s a . a) (\<lambda> s . bogus) (\<lambda> f x . f x)" 

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
  "('x, 'a :: Bogus, 'a md_triv, ('x \<Rightarrow> 'a \<Rightarrow> 'a)) lifting" where
"triv_l =
  LMake (\<lambda> s a _ . mdt a) (\<lambda> s b . (case b of (mdt b') \<Rightarrow> b')) (\<lambda> s . mdt bogus) (\<lambda> f x . f x)"

interpretation triv_l : 
  lifting_valid_weak "(triv_l :: ('x, 'a :: Bogus, 'a md_triv , 'x \<Rightarrow> 'a \<Rightarrow> 'a) lifting)" "\<lambda> _ . UNIV"
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

(* TODO: make sure that using the same namespace here hasn't cost us generality. *)
interpretation triv_l:
  lifting_valid_weak_ok "(triv_l :: ('x, 'a :: {Bogus, Okay}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
  show "\<And> S . ok_S \<subseteq> UNIV" by auto
next
  fix s a b
  show "b \<in> ok_S \<Longrightarrow> LUpd triv_l s a b \<in> ok_S"
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
                Some b' \<Rightarrow> Some (LUpd t s a b')
                | None \<Rightarrow> Some (LUpd t s a (LBase t s))))
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
  fix s a b
  (*assume "b \<in> option_l_S S s"*)
  show "b <[ LUpd (option_l l) s a b"
    using get_put
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
  then show "LUpd (option_l l) s a b \<in> ok_S"
    using ok_S_put
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
                             mdp m b' \<Rightarrow> mdp (f1 s m) (LUpd t s a b')))
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

locale prio_l_valid = prio_l_valid_weak + lifting_valid

sublocale prio_l_valid \<subseteq> out : lifting_valid "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a
  fix b :: "'c md_prio"
(*
  assume H : "b \<in> prio_l_S S s"
*)
  obtain b' pb'  where B' : "b = mdp pb' b'"
    by(cases b; auto)

(*
  have H' : "b' \<in> S s"
    using H B'
    by(auto simp add: prio_l_S_def)
*)
  show "b <[ LUpd (prio_l f0 f1 l) s a b"
    using get_put B' f1_nondecrease
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

locale prio_l_valid_strong = prio_l_valid_weak + prio_l_valid_strong'
sublocale prio_l_valid_strong \<subseteq> out : lifting_valid "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a 
  fix b :: "'c md_prio"
(*  assume H: "b \<in> prio_l_S S s"*)
  obtain x1 p where B : "b = mdp p x1" by(cases b; auto)

  show " b <[ LUpd (prio_l f0 f1 l) s a b"
    using B f1_increase[of p s]
    by(auto simp add:prio_l_def LNew_def prio_pleq split:md_prio.splits)
qed

locale prio_l_valid_stronger = prio_l_valid_strong + prio_l_valid_stronger'
sublocale prio_l_valid_stronger \<subseteq> out : lifting_valid "prio_l f0 f1 l" "S'"
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

  then have Prod_in' : "mdp (f1 s x1) (LUpd l s a x2) \<in> S' s"
    using S'[of s] by auto

  then show "LUpd (prio_l f0 f1 l) s a b \<in> S' s" using B
    by(auto simp add: prio_l_def prio_l_S_def split: md_prio.splits)
next
  fix s a 
  fix b :: "('c md_prio)"

  obtain x1 x2 where B : "b = mdp x1 x2"
    by(cases b; auto)
  (*assume In : "b \<in> S' s"*)
  then show "b <[ LUpd (prio_l f0 f1 l) s a b"
    using f1_increase[of x1 s] B
    by(auto simp add:prio_l_def LNew_def prio_pleq split:md_prio.splits)
qed


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

locale prio_l_valid_base = prio_l_valid_weak_base + lifting_valid

sublocale prio_l_valid_base \<subseteq> out : lifting_valid_base "prio_l f0 f1 l" "prio_l_S S"
proof
  fix s a
  fix b :: "'c md_prio"
  (*assume "b \<in> prio_l_S S s"*)
  show "b <[ LUpd (prio_l f0 f1 l) s a b"
    using f1_nondecrease get_put
    by(auto simp add: prio_l_def prio_pleq prio_l_S_def split: md_prio.splits)
qed

locale prio_l_valid_strong_base = prio_l_valid_strong + prio_l_valid_base

sublocale prio_l_valid_strong_base \<subseteq> out : lifting_valid_base "prio_l f0 f1 l" "prio_l_S S"
proof
qed

locale prio_l_valid_stronger_base = prio_l_valid_stronger + prio_l_valid_base

sublocale prio_l_valid_stronger_base \<subseteq> out :  lifting_valid_base "prio_l f0 f1 l" "S'"
proof
  fix s
  show "LBase (prio_l f0 f1 l) s = \<bottom>"
    using zero base
    by(auto simp add: prio_l_def prio_pleq prio_l_S_def prio_bot split: md_prio.splits)
qed


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

  show "LUpd (prio_l f0 f1 l) s a b \<in> ok_S"
    using ok_S_put[OF H'] B'
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

locale prio_l_valid_strong_ok = prio_l_valid_weak_ok + prio_l_valid_strong

sublocale prio_l_valid_strong_ok \<subseteq> out : lifting_valid_ok "prio_l f0 f1 l" "prio_l_S S"
proof
qed

locale prio_l_valid_stronger_ok = prio_l_valid_weak_ok + prio_l_valid_stronger


sublocale prio_l_valid_stronger_ok \<subseteq> out : lifting_valid_ok "prio_l f0 f1 l" "S'"
proof
  fix s
  show "ok_S \<subseteq> S' s"
    using S'[of s] ok_S_valid[of s]
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

locale prio_l_valid_strong_base_ok = prio_l_valid_strong_ok + prio_l_valid_strong_base
sublocale prio_l_valid_strong_base_ok \<subseteq> lifting_valid_base_ok "prio_l f0 f1 l" "prio_l_S S"
proof
qed

locale prio_l_valid_stronger_base_ok = prio_l_valid_stronger_ok + prio_l_valid_stronger_base
sublocale prio_l_valid_stronger_base_ok \<subseteq> lifting_valid_base_ok "prio_l f0 f1 l" "S'"
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
locale prio_l_valid_base_ok_pres = prio_l_valid_weak_ok_pres' + prio_l_valid_base_ok + lifting_valid_base_ok_pres
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
  LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (LUpd t s a b1, b2)))
            (\<lambda> s x . (LOut t s (fst x)))
            (\<lambda> s . (LBase t s, \<bottom>))
            (LFD t)"

definition fst_l_S :: "('x, 'b1 :: Pord_Weak) valid_set \<Rightarrow> ('x, ('b1 * 'b2 :: Pord_Weakb)) valid_set" where
"fst_l_S S s =
  { b . case b of (b1, _) \<Rightarrow> (b1 \<in> S s) }"

locale fst_l_valid_weak = lifting_valid_weak

sublocale fst_l_valid_weak \<subseteq> out : lifting_valid_weak "fst_l l" "fst_l_S S"
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

locale fst_l_valid = fst_l_valid_weak + lifting_valid

sublocale fst_l_valid \<subseteq> out : lifting_valid "fst_l l" "fst_l_S S"
proof
  fix s a 
  fix b :: "('c :: Pord_Weak) * ('e :: Pord_Weakb)"
  (*assume  Hb : "b \<in> fst_l_S S s"*)
  show "b <[ LUpd (fst_l l) s a b"
    using get_put
    by(auto simp add: fst_l_def prod_pleq fst_l_S_def leq_refl split:prod.splits)
qed

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
      LMake (\<lambda> s a b . (case b of (b1, b2) \<Rightarrow> (b1, LUpd t s a b2)))
            (\<lambda> s x . (LOut t s (snd x)))
            (\<lambda> s . (\<bottom>, LBase t s))
            (LFD t)"

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

locale snd_l_valid = snd_l_valid_weak + lifting_valid

sublocale snd_l_valid \<subseteq> out : lifting_valid "snd_l l" "snd_l_S S"
proof
  fix s a 
  fix b :: "('e :: Pord_Weakb) * ('c :: Pord_Weak)"
  (*assume  Hb : "b \<in> snd_l_S S s"*)
  show "b <[ LUpd (snd_l l) s a b"
    using get_put
    by(auto simp add: snd_l_def prod_pleq leq_refl snd_l_S_def split:prod.splits)
qed

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
 *)

definition merge_l ::
  "('x, 'a1, 'b :: Mergeable, 'f1) lifting \<Rightarrow>
   ('x, 'a2, 'b :: Mergeable, 'f2) lifting \<Rightarrow>
   ('x, 'a1 * 'a2, 'b, 'f1 * 'f2) lifting" where
"merge_l t1 t2 =
    LMake
      (\<lambda> s a b . 
        (case a of (a1, a2) \<Rightarrow>
          [^ LUpd t1 s a1 b, LUpd t2 s a2 b ^]))
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

print_locale merge_l_valid_weak

sublocale merge_l_valid_weak \<subseteq> out : lifting_valid_weak "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s
  fix a :: "'b * 'e"
  fix b :: "'c"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  then obtain supr where Supr : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr"
    using compat[of s a1 b]
    by(auto simp add: has_sup_def)

  have Eq: "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = supr"
    using is_sup_unique[OF bsup_sup[OF Supr bsup_spec] Supr] by simp

  show "LOut (merge_l l1 l2) s (LUpd (merge_l l1 l2) s a b) = a" 
    using compat_get1[OF Supr] compat_get2[OF Supr]
    using A Eq
    by(auto simp add: merge_l_def)
    (* TODO: looks like we need some kind of put2_get1 like rules here. this means our trick
of combining liftings using merge_l may not work. maybe we just bite the bullet and deal
with the n^2 blowup? *)
next
  fix s b

  assume B: "b \<in> S1 s \<inter> S2 s"

  hence B1 : "b \<in> S1 s" by auto

  have "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  then obtain supr where Supr : "is_sup {LUpd l1 s (LOut l1 s b) b, LUpd l2 s (LOut l2 s b) b} supr"
(*    using compat[of b b b s "(LOut l1 s b)" "(LOut l2 s b)"] *)
    using compat[of s "LOut l1 s b" b "LOut l2 s b"]
    by(auto simp add: has_sup_def)

  have Eq : "[^ LUpd l1 s (LOut l1 s b) b, LUpd l2 s (LOut l2 s b) b ^] = supr"
    using is_sup_unique[OF bsup_sup[OF Supr bsup_spec] Supr] by simp

  have B_leq1 : "b <[ LUpd l1 s (LOut l1 s b) b"
    using in1.get_put_weak[OF B1] by auto

  have Upd_leq1 : "LUpd l1 s (LOut l1 s b) b <[ supr"
    using is_supD1[OF Supr] by auto

  have "b <[ supr" using leq_trans[OF B_leq1 Upd_leq1] by simp

  then show "b <[ LUpd (merge_l l1 l2) s (LOut (merge_l l1 l2) s b) b" using Eq
    by(auto simp add: merge_l_def)
next
  fix s 
  fix a :: "'b * 'e"
  fix b :: "'c"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

  have "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  then obtain supr where Supr : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr"
    using compat[of  s "a1" b "a2"]
    by(auto simp add: has_sup_def)

  have Eq : "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = supr"
    using is_sup_unique[OF bsup_sup[OF Supr bsup_spec] Supr] by simp

  have In1 :"supr \<in> S1 s" and In2 : "supr \<in> S2 s" using compat_S[OF Supr]
    by auto

  show "LUpd (merge_l l1 l2) s a b \<in> S1 s \<inter> S2 s" 
    using In1 In2 A Eq
    by(auto simp add: merge_l_def)
qed

locale merge_l_valid = merge_l_valid_weak +
  in1 : lifting_valid l1 S1 +
  in2 : lifting_valid l2 S2

sublocale merge_l_valid \<subseteq> out : lifting_valid "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s
  fix a :: "'b * 'e"
  fix b :: "'c"

  obtain a1 a2 where A: "a = (a1, a2)"
    by(cases a; auto)

(*  assume "b \<in> S1 s \<inter> S2 s"

  hence B1 : "b \<in> S1 s" by auto*)

  have "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  then obtain supr where Supr : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr"
    using compat[of s "a1" b "a2"]
    by(auto simp add: has_sup_def)

  have Eq : "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = supr"
    using is_sup_unique[OF bsup_sup[OF Supr bsup_spec] Supr] by simp

  have B_leq1 : "b <[ LUpd l1 s a1 b"
    using in1.get_put by auto

  have Upd_leq1 : "LUpd l1 s a1 b <[ supr"
    using is_supD1[OF Supr] by auto

  have "b <[ supr" using leq_trans[OF B_leq1 Upd_leq1] by simp

  then show "b <[ LUpd (merge_l l1 l2) s a b" using A Eq
    by(auto simp add: merge_l_def)
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

  have "is_sup {b, b} b"
    by(auto simp add: is_sup_def is_least_def is_ub_def leq_refl)

  then obtain supr where Supr : "is_sup {LUpd l1 s a1 b, LUpd l2 s a2 b} supr"
    using compat[of s "a1" b "a2"]
    by(auto simp add: has_sup_def)

  have Eq : "[^ LUpd l1 s a1 b, LUpd l2 s a2 b ^] = supr"
    using is_sup_unique[OF bsup_sup[OF Supr bsup_spec] Supr] by simp

  show "LUpd (merge_l l1 l2) s a b \<in> ok_S"
    using compat_ok[OF  B_ok Supr] Eq A
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

locale merge_l_valid_weak_pres = merge_l_valid_weak +
  in1 : lifting_valid_weak_pres l1 S1 +
  in2 : lifting_valid_weak_pres l2 S2

sublocale merge_l_valid_weak_pres \<subseteq> out: lifting_valid_weak_pres "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof

  term "l1"

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
(*
maybe we need to restrict f to functions that are already sups_pres?
*)

  show "is_sup (LMap (merge_l l1 l2) f s ` V) (LMap (merge_l l1 l2) f s supr)"
  proof(rule is_supI)
    fix xo

    assume Xo: "xo \<in> LMap (merge_l l1 l2) f s ` V"


    then obtain xi where Xi : "xi \<in> V" 
     "xo = [^ LMap l1 f1 s xi, LMap l2 f2 s xi^]"
      using F
      by(auto simp add: merge_l_def split: prod.splits)

    then obtain xo' where Xo' : "is_sup {LMap l1 f1 s xi, LMap l2 f2 s xi} xo'"
      using compat[of s ]
      by(fastforce simp add:has_sup_def)

    then have Xo_sup : "is_sup {LMap l1 f1 s xi, LMap l2 f2 s xi} xo"
      using bsup_sup[OF Xo' bsup_spec] Xi
      by auto

    obtain res' where Res' : "is_sup {LMap l1 f1 s supr, LMap l2 f2 s supr} res'"
      using compat[of s]
      by(fastforce simp add: has_sup_def)

    have Res_sup : "is_sup {LMap l1 f1 s supr, LMap l2 f2 s supr} [^ LMap l1 f1 s supr, LMap l2 f2 s supr ^]"
      using bsup_sup[OF Res' bsup_spec] 
      by(auto)

    have "xi <[ supr"
      using is_supD1[OF Supr Xi(1)] by simp

    have Ubx : "is_ub {LMap l1 f1 s xi, LMap l2 f2 s xi} 
      [^ LMap l1 f1 s supr, LMap l2 f2 s supr ^]"
    proof(rule is_ubI)
      fix x

      assume X: "x \<in> {LMap l1 f1 s xi, LMap l2 f2 s xi}"

      then consider (X1) "x = LMap l1 f1 s xi" |
                    (X2) "x = LMap l2 f2 s xi" by auto

      then show " x <[ [^ LMap l1 f1 s supr, LMap l2 f2 s supr ^]"
      proof cases
        case X1

        have Xi_sup : "is_sup {xi, supr} supr"
          using is_sup_pair[OF `xi <[ supr`] by simp

        have Map_sup : "is_sup (LMap l1 f1 s ` V) (LMap l1 f1 s supr)"
          using in1.pres[OF Vin Vsub1 Supr Supr_in1, of f1]
          by simp

        have F1_map : "LMap l1 f1 s xi \<in> LMap l1 f1 s ` V "
          using imageI[OF Xi(1), of "LMap l1 f1 s"] Xi  X1
          by(auto)

        have Leq1 : "LMap l1 f1 s xi <[ (LMap l1 f1 s supr)" using is_supD1[OF Map_sup F1_map] 
          by auto

        have Leq2 :"LMap l1 f1 s supr <[ [^ LMap l1 f1 s supr, LMap l2 f2 s supr ^]"
          using is_supD1[OF Res_sup]
          by auto

        show ?thesis using leq_trans[OF Leq1 Leq2] X1
          by auto
      next

        case X2
          
        have Xi_sup : "is_sup {xi, supr} supr"
          using is_sup_pair[OF `xi <[ supr`] by simp

        have Map_sup : "is_sup (LMap l2 f2 s ` V) (LMap l2 f2 s supr)"
          using in2.pres[OF Vin Vsub2 Supr Supr_in2, of f2]
          by simp

        have F2_map : "LMap l2 f2 s xi \<in> LMap l2 f2 s ` V "
          using imageI[OF Xi(1), of "LMap l2 f2 s"] Xi  X2
          by(auto)

        have Leq1 : "LMap l2 f2 s xi <[ (LMap l2 f2 s supr)" using is_supD1[OF Map_sup F2_map] 
          by auto

        have Leq2 :"LMap l2 f2 s supr <[ [^ LMap l1 f1 s supr, LMap l2 f2 s supr ^]"
          using is_supD1[OF Res_sup]
          by auto

        show ?thesis using leq_trans[OF Leq1 Leq2] X2
          by auto

      qed
    qed

    show "xo <[ LMap (merge_l l1 l2) f s supr" 
      using is_supD2[OF Xo_sup Ubx] F
      by(auto simp add: merge_l_def)
  next

    fix x'

    assume X' : "is_ub (LMap (merge_l l1 l2) f s ` V) x'"

    obtain res' where Res' : "is_sup {LMap l1 f1 s supr, LMap l2 f2 s supr} res'"
      using compat[of s]
      by(fastforce simp add: has_sup_def)

    have Res_sup : "is_sup {LMap l1 f1 s supr, LMap l2 f2 s supr} [^ LMap l1 f1 s supr, LMap l2 f2 s supr ^]"
      using bsup_sup[OF Res' bsup_spec] 
      by(auto)

    have Ub: "is_ub {LMap l1 f1 s supr, LMap l2 f2 s supr} x'"
    proof(rule is_ubI)

      fix x

      assume "x \<in> {LMap l1 f1 s supr, LMap l2 f2 s supr}"

      then consider (1) "x = LMap l1 f1 s supr" | 
                    (2) "x = LMap l2 f2 s supr"
        by blast

      then show "x <[ x'"
      proof cases
        case 1

        have Map_sup : "is_sup (LMap l1 f1 s ` V) (LMap l1 f1 s supr)"
          using in1.pres[OF Vin Vsub1 Supr Supr_in1, of f1]
          by simp

        have Ub : "is_ub (LMap l1 f1 s ` V) (x')"
        proof(rule is_ubI)

          fix w

          assume W: "w \<in> LMap l1 f1 s ` V"

          then obtain w' where W' : "w' \<in> V" "LMap l1 f1 s w' = w"
            by auto

          obtain res_w where Resw : "is_sup {LMap l1 f1 s w', LMap l2 f2 s w'} res_w"
            using compat[of s]
            by(fastforce simp add: has_sup_def)

          have Resw_sup : "is_sup {LMap l1 f1 s w', LMap l2 f2 s w'} [^ LMap l1 f1 s w', LMap l2 f2 s w' ^]"
            using bsup_sup[OF Resw bsup_spec] 
            by(auto)

          have Leq1 : "w <[ LMap (merge_l l1 l2) f s w'"
            using is_supD1[OF Resw_sup, of w] W' F
            by(auto simp add: merge_l_def)

          have Map_in : "LMap (merge_l l1 l2) f s w' \<in> LMap (merge_l l1 l2) f s ` V"
            using imageI[OF W'(1)] by auto

          have Leq2 : "LMap (merge_l l1 l2) f s w' <[ x'"
            using is_ubE[OF X' Map_in] F
            by(auto simp add: merge_l_def)

          then show "w <[ x'"
            using leq_trans[OF Leq1 Leq2]
            by auto
        qed

        show "x <[ x'"
          using is_supD2[OF Map_sup Ub] 1
          by auto
      next

        case 2
        have Map_sup : "is_sup (LMap l2 f2 s ` V) (LMap l2 f2 s supr)"
          using in2.pres[OF Vin Vsub2 Supr Supr_in2, of f2]
          by simp

        have Ub : "is_ub (LMap l2 f2 s ` V) (x')"
        proof(rule is_ubI)

          fix w

          assume W: "w \<in> LMap l2 f2 s ` V"

          then obtain w' where W' : "w' \<in> V" "LMap l2 f2 s w' = w"
            by auto

          obtain res_w where Resw : "is_sup {LMap l1 f1 s w', LMap l2 f2 s w'} res_w"
            using compat[of s]
            by(fastforce simp add: has_sup_def)

          have Resw_sup : "is_sup {LMap l1 f1 s w', LMap l2 f2 s w'} [^ LMap l1 f1 s w', LMap l2 f2 s w' ^]"
            using bsup_sup[OF Resw bsup_spec] 
            by(auto)

          have Leq1 : "w <[ LMap (merge_l l1 l2) f s w'"
            using is_supD1[OF Resw_sup, of w] W' F
            by(auto simp add: merge_l_def)

          have Map_in : "LMap (merge_l l1 l2) f s w' \<in> LMap (merge_l l1 l2) f s ` V"
            using imageI[OF W'(1)] by auto

          have Leq2 : "LMap (merge_l l1 l2) f s w' <[ x'"
            using is_ubE[OF X' Map_in] F
            by(auto simp add: merge_l_def)

          then show "w <[ x'"
            using leq_trans[OF Leq1 Leq2]
            by auto
        qed

        show "x <[ x'"
          using is_supD2[OF Map_sup Ub] 2
          by auto
      qed
    qed

    show "LMap (merge_l l1 l2) f s supr <[ x'"
      using is_supD2[OF Res_sup Ub] F
      by(auto simp add: merge_l_def)
  qed
qed

locale option_l_ortho =
  l_ortho (*+
  in1 : option_l_valid_weak l1 S1 +
  in2 : option_l_valid_weak l2 S2 *)

lemma is_sup_Some :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup (Some ` Xs) (Some supr)"
proof(rule is_supI)
  fix z
  assume Z : "z \<in> Some ` Xs"
  then obtain z' where Z' : "z = Some z'" "z' \<in> Xs"
    by auto

  show "z <[ Some supr"
    using is_supD1[OF H Z'(2)] Z'(1)
    by(auto simp add: option_pleq)
next
  fix w
  assume Ub : "is_ub (Some ` Xs) w"

  have "Some x \<in> Some ` Xs"
    using Hnemp by auto

  then have "Some x <[ w"
    using is_ubE[OF Ub]
    by auto

  then obtain w' where W' : "w = Some w'"
    by(cases w; auto simp add: option_pleq)

  have "is_ub Xs w'"
  proof
    fix z'

    assume Z': "z' \<in> Xs"

    then have "Some z' \<in> Some ` Xs"
      by auto

    then have "Some z' <[ w"
      using is_ubE[OF Ub] by auto

    then show "z' <[ w'" using W' by(auto simp add: option_pleq)
  qed

  then have "supr <[ w'"
    using is_supD2[OF H] by auto

  then show "Some supr <[ w"
    using W' by(auto simp add: option_pleq)
qed

lemma is_sup_Some' :
  assumes Hnemp : "x \<in> Xs"
  assumes H: "is_sup (Some ` Xs) (Some supr)"
  shows "is_sup Xs supr"
proof(rule is_supI)
  fix z

  assume Z: "z \<in> Xs"

  then have "Some z <[ Some supr"
    using is_supD1[OF H, of "Some z"] by auto

  then show "z <[ supr"
    by(simp add: option_pleq)
next

  fix w

  assume Ub : "is_ub Xs w"

  have "is_ub (Some ` Xs) (Some w)"
  proof(rule is_ubI)

    fix z'
    assume Z' : "z' \<in> Some ` Xs"

    then obtain z where Z: "z' = Some z" "z \<in> Xs"
      by auto

    have "z <[ w" using is_ubE[OF Ub Z(2)]
      by auto

    then show "z' <[ Some w"
      using Z by(auto simp add: option_pleq)
  qed

  then have "Some supr <[ Some w"
    using is_supD2[OF H] by auto

  then show "supr <[ w"
    by(auto simp add: option_pleq)
qed

sublocale option_l_ortho \<subseteq> out : l_ortho "option_l l1"  "option_l_S S1" "option_l l2" "option_l_S S2"
proof
  fix s
  show "LBase (option_l l1) s = LBase (option_l l2) s"
    by(auto simp add: option_l_def)
next

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

  fix b s
  fix a1 :: 'b
  fix a2 :: 'e
  fix supr

  assume Sup: "is_sup {LUpd (option_l l1) s a1 b, LUpd (option_l l2) s a2 b} supr"

  obtain r1 where R1: "LUpd (option_l l1) s a1 b = Some r1"
    by(cases b; auto simp add: option_l_def)

  obtain r2 where R2 : "LUpd (option_l l2) s a2 b = Some r2"
    by(cases b; auto simp add: option_l_def)

  show "supr \<in> option_l_S S1 s \<inter> option_l_S S2 s"
  proof(cases supr)
    case None

    then have "Some r1 <[ None"
      using is_supD1[OF Sup, of "Some r1"] unfolding R1 None
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

    show ?thesis
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

      have "supr' \<in> S1 s \<inter> S2 s"
        using compat_S Sup_inner[unfolded sym[OF R1']
                                ,unfolded sym[OF R2']
                                ,unfolded Bases]
        by auto
        
      then show ?thesis 
        using Some
        by(auto simp add: option_l_S_def)
    next
      case Some' : (Some b')

      have R1' : "LUpd l1 s a1 b' = r1"
        using Some' R1
        by(auto simp add: option_l_def)

      have R2' : "LUpd l2 s a2 b' = r2"
        using Some' R2
        by(auto simp add: option_l_def)

      have "supr' \<in> S1 s \<inter> S2 s"
        using compat_S Sup_inner R1' R2'
        by(auto)

      then show ?thesis
        using Some
        by(auto simp add: option_l_S_def)
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
qed

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

lemma is_sup_fst :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup ((\<lambda> w . (w, x')) ` Xs) (supr, x')"
proof(rule is_supI)
  fix x

  assume X: "x \<in> (\<lambda>w. (w, x')) ` Xs"

  then obtain x1 where X1 :
    "x = (x1, x')" "x1 \<in> Xs"
    by auto

  have "x1 <[ supr"
    using is_supD1[OF H X1(2)] by auto

  then show "x <[ (supr, x')"
    using X1
    by(auto simp add: prod_pleq leq_refl)
next

  fix y

  assume Y: "is_ub ((\<lambda>w. (w, x')) ` Xs) y"

  obtain y1 y2 where Y1_2 : "y = (y1, y2)"
    by(cases y; auto)

  have "is_ub Xs y1"
  proof(rule is_ubI)
    fix z

    assume Z: "z \<in> Xs"

    then have "(z, x') <[ y"
      using is_ubE[OF Y] by auto

    then show "z <[ y1"
      using Y1_2
      by(auto simp add: prod_pleq)
  qed

  then have "supr <[ y1"
    using is_supD2[OF H]
    by auto

  have "(x, x') <[ y"
    using is_ubE[OF Y] Hnemp
    by auto

  then have "x' <[ y2"
    using Y1_2
    by(auto simp add: prod_pleq)

  show "(supr, x') <[ y"
    using `supr <[ y1` `x' <[ y2` Y1_2
    by(auto simp add: prod_pleq)
qed

lemma is_sup_fst' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_sup Xys (s1, s2)"
  shows "is_sup (fst ` Xys) s1"
proof(rule is_supI)

  fix x

  assume X: "x \<in> fst ` Xys"
  then obtain y where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_supD1[OF H Xy]
    by auto

  then show "x <[ s1"
    by(auto simp add: prod_pleq)
next

  fix x'

  assume X' : "is_ub (fst ` Xys) x'"

  have Ub' : "is_ub Xys (x', s2)"
  proof(rule is_ubI)

    fix w

    assume W : "w \<in> Xys"

    obtain w1 w2 where W1_2 :
      "w = (w1, w2)"
      by(cases w; auto)

    then have "w1 \<in> fst ` Xys" using imageI[OF W, of fst]
      by auto

    then have "w1 <[ x'"
      using is_ubE[OF X'] by auto

    have "w2 \<in> snd ` Xys" using imageI[OF W, of snd] W1_2
      by auto

    then have "w2 <[ s2"
      using is_supD1[OF H W] W1_2
      by(auto simp add: prod_pleq)

    then show "w <[ (x', s2)"
      using `w1 <[ x'` W1_2
      by(auto simp add: prod_pleq)
  qed

  show "s1 <[ x'"
    using is_supD2[OF H Ub']
    by(auto simp add: prod_pleq)
qed


lemma is_sup_snd :
  assumes Hnemp : "x \<in> Xs"
  assumes H : "is_sup Xs supr"
  shows "is_sup ((\<lambda> w . (x', w)) ` Xs) (x', supr)"
proof(rule is_supI)
  fix x

  assume X: "x \<in> (\<lambda>w. (x', w)) ` Xs"

  then obtain x2 where X2 :
    "x = (x', x2)" "x2 \<in> Xs"
    by auto

  have "x2 <[ supr"
    using is_supD1[OF H X2(2)] by auto

  then show "x <[ (x', supr)"
    using X2
    by(auto simp add: prod_pleq leq_refl)
next

  fix y

  assume Y: "is_ub ((\<lambda>w. (x', w)) ` Xs) y"

  obtain y1 y2 where Y1_2 : "y = (y1, y2)"
    by(cases y; auto)

  have "is_ub Xs y2"
  proof(rule is_ubI)
    fix z

    assume Z: "z \<in> Xs"

    then have "(x', z) <[ y"
      using is_ubE[OF Y] by auto

    then show "z <[ y2"
      using Y1_2
      by(auto simp add: prod_pleq)
  qed

  then have "supr <[ y2"
    using is_supD2[OF H]
    by auto

  have "(x', x) <[ y"
    using is_ubE[OF Y] Hnemp
    by auto

  then have "x' <[ y1"
    using Y1_2
    by(auto simp add: prod_pleq)

  show "(x', supr) <[ y"
    using `supr <[ y2` `x' <[ y1` Y1_2
    by(auto simp add: prod_pleq)
qed

lemma is_sup_snd' :
  assumes Hnemp : "xy \<in> Xys"
  assumes H : "is_sup Xys (s1, s2)"
  shows "is_sup (snd ` Xys) s2"
proof(rule is_supI)

  fix y

  assume Y: "y \<in> snd ` Xys"
  then obtain x where Xy : "(x, y) \<in> Xys"
    by(auto)

  then have "(x, y) <[ (s1, s2)"
    using is_supD1[OF H Xy]
    by auto

  then show "y <[ s2"
    by(auto simp add: prod_pleq)
next

  fix y'

  assume Y' : "is_ub (snd ` Xys) y'"

  have Ub' : "is_ub Xys (s1, y')"
  proof(rule is_ubI)

    fix w

    assume W : "w \<in> Xys"

    obtain w1 w2 where W1_2 :
      "w = (w1, w2)"
      by(cases w; auto)

    then have "w2 \<in> snd ` Xys" using imageI[OF W, of snd]
      by auto

    then have "w2 <[ y'"
      using is_ubE[OF Y'] by auto

    have "w1 \<in> fst ` Xys" using imageI[OF W, of fst] W1_2
      by auto

    then have "w1 <[ s1"
      using is_supD1[OF H W] W1_2
      by(auto simp add: prod_pleq)

    then show "w <[ (s1, y')"
      using `w2 <[ y'` W1_2
      by(auto simp add: prod_pleq)
  qed

  show "s2 <[ y'"
    using is_supD2[OF H Ub']
    by(auto simp add: prod_pleq)
qed


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

  show "supr \<in> fst_l_S S1 s \<inter> fst_l_S S2 s"
    using compat_S[OF Sup'] S
    by(auto simp add: fst_l_S_def)

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
    
(* use is_sup_unique here to show that it is the two components. *)
  have Conc1 : "supr1 \<in> S1 s"
    using Sup1_2 Sup_eq
    in1.put_S
    by(auto)

  have Conc2 : "supr2 \<in> S2 s"
    using Sup1_2 Sup_eq
    in2.put_S
    by auto

  show "supr
       \<in> fst_l_S S1 s \<inter>
          snd_l_S S2 s"
    using Conc1 Conc2 Sup1_2
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

(* lifting_valid_weak_ok *)
locale fst_l_snd_l_ortho_ok =
  fst_l_snd_l_ortho + 
  in1 : lifting_valid_weak_ok l1 S1 +
  in2 : lifting_valid_weak_ok l2 S2

sublocale fst_l_snd_l_ortho_ok \<subseteq> out : l_ortho_ok "fst_l l1" "fst_l_S S1" "snd_l l2" "snd_l_S S2"
proof

  term "l1"
  term "l2"

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

(*
ortho_base
ortho_ok
*)

(*

*)

(* next steps:
- relating sups_pres and ortho?
- making sure we can actually do everything we need with the new implementation.
*)

(*
  next up: ortho instances (and ortho_base, and ortho_ok, and
  ortho_base_ok

- option
- prio?
- fst, fst
- snd, snd
- fst, snd
- merge
*)



end