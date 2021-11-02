theory Lifter_Instances imports Lifter "../Mergeable/Mergeable_Facts"
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

locale option_l_valid_clos = lifting_valid_weak_clos + option_l_valid_weak

sublocale option_l_valid_clos \<subseteq> lifting_valid_weak_clos "option_l l" "option_l_S S"
proof
  fix a b s
  assume A: "a \<in> option_l_S S s"
  then obtain a' where A' : "a = Some a'" "a' \<in> S s"
    by(cases a; auto simp add: option_l_S_def)

  assume Leq : "a <[ b"
  then obtain b' where B' : "b = Some b'" "a' <[ b'"
    using A A'
    by(cases b; auto simp add: option_pleq)

  show "b \<in> option_l_S S s"
    using A' Leq clos_S[OF B'(2) A'(2)] B'
    by(auto simp add: option_l_S_def option_pleq)
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

locale fst_l_valid_clos = lifting_valid_weak_clos + fst_l_valid_weak

sublocale fst_l_valid_clos \<subseteq> lifting_valid_weak_clos "fst_l l" "fst_l_S S"
proof
  fix s
  fix a b :: "('c * 'e)"
  assume Leq : "a <[ b"
  assume Ain : "a \<in> fst_l_S S s"

  then obtain a1 a2 where A' : "a = (a1, a2)" "a1 \<in> S s"
    by(cases a; auto simp add: fst_l_S_def)

  obtain b1 b2 where B' : "b = (b1, b2)" "a1 <[ b1"
    using A' Leq
    by(cases b; auto simp add: prod_pleq)

  then have "b1 \<in> S s"
    using clos_S[OF B'(2) A'(2)] by auto

  then show "b \<in> fst_l_S S s"
    unfolding B'
    by(auto simp add: fst_l_S_def)
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

locale snd_l_valid_clos = lifting_valid_weak_clos + snd_l_valid_weak

sublocale snd_l_valid_clos \<subseteq> lifting_valid_weak_clos "snd_l l" "snd_l_S S"
proof
  fix s
  fix a b :: "('e * 'c)"
  assume Leq : "a <[ b"
  assume Ain : "a \<in> snd_l_S S s"

  then obtain a1 a2 where A' : "a = (a1, a2)" "a2 \<in> S s"
    by(cases a; auto simp add: snd_l_S_def)

  obtain b1 b2 where B' : "b = (b1, b2)" "a2 <[ b2"
    using A' Leq
    by(cases b; auto simp add: prod_pleq)

  then have "b2 \<in> S s"
    using clos_S[OF B'(2) A'(2)] by auto

  then show "b \<in> snd_l_S S s"
    unfolding B'
    by(auto simp add: snd_l_S_def)
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
          LUpd t1 s a1 (LUpd t2 s a2 b )))
      (\<lambda> s b . (LOut t1 s b, LOut t2 s b))
      (\<lambda> s . LBase t1 s)
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

sublocale merge_l_valid_weak \<subseteq> out : lifting_valid_weak "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s
  fix a :: "'b * 'e"
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
  fix a :: "'b * 'e"

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

  have Leq1 : "b <[ LUpd l2 s a2 b"
    using in2.get_put by auto

  have Leq2 : "LUpd l2 s a2 b <[ LUpd l1 s a1 (LUpd l2 s a2 b)"
    using in1.get_put by auto

  show "b <[ LUpd (merge_l l1 l2) s a b" 
    using A leq_trans[OF Leq1 Leq2]
    by(auto simp add: merge_l_def)
qed

locale merge_l_valid_weak_base = merge_l_valid_weak + l_ortho_base +
  in1 : lifting_valid_base l1 S1 +
  in2 : lifting_valid_base l2 S2

sublocale merge_l_valid_weak_base \<subseteq> out : lifting_valid_weak_base "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
  fix s :: "'a"

  show "LBase (merge_l l1 l2) s = \<bottom>"
    using in1.base
    by(auto simp add: merge_l_def)
qed

locale merge_l_valid_base = merge_l_valid + merge_l_valid_weak_base

sublocale merge_l_valid_base \<subseteq> out : lifting_valid_base "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
proof
qed
(*
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
*)

locale merge_l_valid_weak_pres = merge_l_valid_weak +
  l_ortho_pres +
  in1 : lifting_valid_weak_pres l1 S1 +
  in2 : lifting_valid_weak_pres l2 S2

sublocale merge_l_valid_weak_pres \<subseteq> out: lifting_valid_weak_pres "merge_l l1 l2" "\<lambda> x . S1 x \<inter> S2 x"
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


  have Pres1 : "is_sup (LMap l1 f1 s ` V) (LMap l1 f1 s supr)"
    using in1.pres[OF Vin Vsub1 Supr Supr_in1, of f1]
    by(auto)

  have In1 : "LMap l1 f1 s supr \<in> S1 s \<inter> S2 s"
    using in1.put_S put1_S2[OF Supr_in2]
    by auto

  have Pres2 : "is_sup (LMap l2 f2 s ` V) (LMap l2 f2 s supr)"
    using in2.pres[OF Vin Vsub2 Supr Supr_in2, of f2]
    by(auto)

  have In2 : "LMap l2 f2 s supr \<in> S1 s \<inter> S2 s"
    using in2.put_S put2_S1[OF Supr_in1]
    by auto

  have PresFull_1 : "is_sup (LMap l1 f1 s ` (LMap l2 f2 s ` V)) (LMap l1 f1 s (LMap l2 f2 s supr))"
    using compat_pres1[OF Vin Vsub1 Vsub2 Pres1 In1 Pres2 In2] by auto

  have Merge_Eq1 : "LMap (merge_l l1 l2) f s supr = (LMap l1 f1 s (LMap l2 f2 s supr))"
    using F
    by(auto simp add: merge_l_def put1_get2 put2_get1)

  have Merge_Eq2 : "LMap (merge_l l1 l2) f s supr = (LMap l2 f2 s (LMap l1 f1 s supr))"
    using F
    by(auto simp add: merge_l_def put1_get2 put2_get1 compat)

  have Eq : "(LMap l1 f1 s ` (LMap l2 f2 s ` V)) = (LMap (merge_l l1 l2) f s ` V)"
    using F
    unfolding image_image
    by(auto simp add: merge_l_def put1_get2 put2_get1)

  have Eq2 : "(LMap (merge_l l1 l2) f s supr) = LMap l1 f1 s (LMap l2 f2 s supr)"
    using F
    by(auto simp add: merge_l_def put1_get2 put2_get1)

  show " is_sup
        (LMap (merge_l l1 l2) f s ` V)
        (LMap (merge_l l1 l2) f s supr)"
    using PresFull_1
    unfolding Eq2
    unfolding F Eq
    by simp
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

  fix b s 
  fix a1 :: 'b
  fix a2 :: 'e

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

  have Some_map3 : "LMap (option_l l2) f2 s ` Some ` LMap l1 f1 s ` V' = Some ` LMap l2 f2 s ` LMap l1 f1 s ` V'"
  proof
    show "LMap (option_l l2) f2 s ` Some ` LMap l1 f1 s ` V' \<subseteq> Some ` LMap l2 f2 s ` LMap l1 f1 s ` V'"
      using Vv'
      by(auto simp add: option_l_def)
  next
    show "Some ` LMap l2 f2 s ` LMap l1 f1 s ` V' \<subseteq> LMap (option_l l2) f2 s ` Some ` LMap l1 f1 s ` V'"
    proof
      fix x
      assume X: "x \<in> Some ` LMap l2 f2 s ` LMap l1 f1 s ` V'"

      then obtain xo where Xo : "xo \<in> V'" "x = Some (LMap l2 f2 s (LMap l1 f1 s xo))"
        by auto

      then have X_eq : "x = LMap (option_l l2) f2 s (Some (LMap l1 f1 s xo))"
        using Vv'
        by(auto simp add: option_l_def)

      have Xo_in : "Some xo \<in> V"
        using Xo Vv' by auto

      have Xo_in' : "Some (LMap l1 f1 s xo) \<in> Some ` LMap l1 f1 s ` V'"
        using Xo
        by auto

      show "x \<in> LMap (option_l l2) f2 s ` Some ` LMap l1 f1 s ` V'"
        using imageI[OF Xo_in', of "LMap (option_l l2) f2 s"] X Xo
        by(auto simp add: option_l_def)
    qed
  qed

  show "is_sup (LMap (option_l l2) f2 s ` LMap (option_l l1) f1 s ` V) (LMap (option_l l2) f2 s s1)"
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

      have Conc' : "is_sup (LMap l2 f2 s ` LMap l1 f1 s ` V') (LMap l2 f2 s s1')"
        using compat_pres2[OF V'(1) V'sub1 V'sub2 Sup'1 Sin1' Sup'2 Sin2']
        by auto

      show "is_sup
          (LMap (option_l l2) f2 s ` LMap (option_l l1) f1 s ` V)
          (LMap (option_l l2) f2 s s1)"
      proof(rule is_supI)
        fix z

        assume Z: "z \<in> LMap (option_l l2) f2 s `
             LMap (option_l l1) f1 s ` V "

        then have Z1 : "z \<in> LMap (option_l l2) f2 s `
             (Some ` LMap l1 f1 s ` V')"
          using Some_map1
          by auto

        then obtain z' where Z2 : "z = Some z'" "z' \<in> LMap l2 f2 s ` LMap l1 f1 s ` V'"
          unfolding Some_map3
          by auto

        show "z <[ LMap (option_l l2) f2 s s1"
          using is_supD1[OF Conc' Z2(2)] Some' Z2(1) Some
          by(auto simp add: option_l_def option_pleq)
      next

        fix w

        assume Ub : "is_ub (LMap (option_l l2) f2 s ` LMap (option_l l1) f1 s ` V) w"

        then have Ub1 : "is_ub (LMap (option_l l2) f2 s `
             (Some ` LMap l1 f1 s ` V')) w"
          using Some_map1
          by auto

        show "LMap (option_l l2) f2 s s1 <[ w"
        proof(cases w)
          case None'' : None

          have In' : "LMap (option_l l2) f2 s (Some (LMap l1 f1 s v')) \<in> LMap (option_l l2) f2 s ` Some ` LMap l1 f1 s ` V' "
            using imageI[OF V'(1), of "LMap (option_l l2) f2 s o Some o LMap l1 f1 s"]
            by auto

          have False using is_ubE[OF Ub1 In'] None''
            by(auto simp add: option_l_def option_pleq)

          then show ?thesis by auto
        next
          case Some'' : (Some w')
          have Ub2 : "is_ub (LMap l2 f2 s ` LMap l1 f1 s ` V') w'"
          proof(rule is_ubI)
            fix k

            assume K: "k \<in> LMap l2 f2 s ` LMap l1 f1 s ` V'"

            then have K' : "Some k \<in> Some ` LMap l2 f2 s ` LMap l1 f1 s ` V'"
              by auto

            show "k <[ w'"
              using is_ubE[OF Ub1, of "Some k"] Some'' K'
              unfolding Some_map3
              by(auto simp add: option_pleq)
          qed
          
          show ?thesis 
            using is_supD2[OF Conc' Ub2] Some'' Some' Some
            by(auto simp add: option_l_def option_pleq)
        qed
      qed
    qed
  qed
next
  fix a1 a2 s x

  show "is_sup {LUpd (option_l l1) s a1 x, LUpd (option_l l2) s a2 x}
        (LUpd (option_l l1) s a1 (LUpd (option_l l2) s a2 x))"
  proof(cases x)
    case None

    have R1 : "LUpd (option_l l1) s a1 x = Some (LUpd l1 s a1 (LBase l1 s))"
      using None
      by(auto simp add: option_l_def)

    have R2 : "LUpd (option_l l2) s a2 x = Some (LUpd l2 s a2 (LBase l2 s))"
      using None
      by(auto simp add: option_l_def)

    have Bases : "LBase l1 s = LBase l2 s"
      using compat_base1 compat_base2 by auto

    then have Conc' : "is_sup (Some ` {(LUpd l1 s a1 (LBase l2 s)),(LUpd l2 s a2 (LBase l2 s))})
     (Some (LUpd l1 s a1 (LUpd l2 s a2 (LBase l2 s))))"
      using is_sup_Some[OF _ compat_pres_sup]
      unfolding R1 R2 Bases
      by(fastforce simp add: option_l_def)

    then show ?thesis using None Bases
      by(auto simp add: option_l_def)
  next
    case (Some x')
    have R1 : "LUpd (option_l l1) s a1 x = Some (LUpd l1 s a1 x')"
      using Some
      by(auto simp add: option_l_def)

    have R2 : "LUpd (option_l l2) s a2 x = Some (LUpd l2 s a2 x')"
      using Some
      by(auto simp add: option_l_def)

    then have Conc' : "is_sup (Some ` {(LUpd l1 s a1 x'),(LUpd l2 s a2 x')})
     (Some (LUpd l1 s a1 (LUpd l2 s a2 x')))"
      using is_sup_Some[OF _ compat_pres_sup]
      unfolding R1 R2 
      by(fastforce simp add: option_l_def)

    then show ?thesis using Some 
      by(auto simp add: option_l_def)
  qed
qed




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

  fix b :: "('c * 'g)"
  fix s
  fix a1 :: 'b
  fix a2 :: 'e

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

  fix b :: "('c * 'g)"
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
  fix b :: "('c * 'g)"
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
  fix b :: "'c * 'g"
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
  fix b :: "'c * 'g"
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
  fix s f1 f2 s1 s2 v 
  fix V :: "('c * 'g) set"

  assume Sup1 : "is_sup (LMap (fst_l l1) f1 s ` V) s1"
  assume Sup2 : "is_sup (LMap (fst_l l2) f2 s ` V) s2"
  assume Vin : "v \<in> V"
  assume Vsub1 : "V \<subseteq> fst_l_S S1 s"
  assume Vsub2 : "V \<subseteq> fst_l_S S2 s"

  assume Sin1 : "s1 \<in> fst_l_S S1 s \<inter> fst_l_S S2 s"
  assume Sin2 : "s2 \<in> fst_l_S S1 s \<inter> fst_l_S S2 s"

  obtain V' where SV' : "V' = { x1 . \<exists> x2 . (x1, x2) \<in> V}"
    by auto

  have V'sub1 : "V' \<subseteq> S1 s"
    using SV' Vsub1
    by(auto simp add: fst_l_S_def)

  have V'sub2 : "V' \<subseteq> S2 s"
    using SV' Vsub2
    by(auto simp add: fst_l_S_def)

  obtain v1 v2 where V' :
    "v1 \<in> V'" "v = (v1, v2)"
    using Vin
    unfolding SV'
    by (cases v; auto)

  obtain s1_1 s1_2 where S1 : "s1 = (s1_1, s1_2)"
    by(cases s1; auto)

  obtain s2_1 s2_2 where S2: "s2 = (s2_1, s2_2)"
    by(cases s2; auto)

  have Sup'1 : "is_sup (LMap l1 f1 s ` V') s1_1"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l1 f1 s ` V'"

    then obtain xo1 where Xo1 : "xo1 \<in> V'" "LMap l1 f1 s xo1 = x"
      by auto

    then obtain xo2 where Xo2 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(x, xo2) \<in> LMap (fst_l l1) f1 s ` V"
      using imageI[OF Xo2, of "LMap (fst_l l1) f1 s"] Xo1
      by(auto simp add: fst_l_def)

    then show "x <[ s1_1"
      using is_supD1[OF Sup1 Xin] using S1
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l1 f1 s ` V') w"

    have Ub' : "is_ub (LMap (fst_l l1) f1 s ` V) (w, s1_2)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (fst_l l1) f1 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (fst_l l1) f1 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo1 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (LMap l1 f1 s zo1, zo2)"
        using Zo
        by(auto simp add: fst_l_def)

      have Conc1 : "LMap l1 f1 s zo1 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo2 <[ s1_2"
        using is_supD1[OF Sup1 Zin] Zo_12 S1 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (w, s1_2)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed

    
    show "s1_1 <[ w"
      using is_supD2[OF Sup1 Ub'] S1
      by(auto simp add: prod_pleq)
  qed

  have Sup'2 : "is_sup (LMap l2 f2 s ` V') s2_1"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l2 f2 s ` V'"

    then obtain xo1 where Xo1 : "xo1 \<in> V'" "LMap l2 f2 s xo1 = x"
      by auto

    then obtain xo2 where Xo2 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(x, xo2) \<in> LMap (fst_l l2) f2 s ` V"
      using imageI[OF Xo2, of "LMap (fst_l l2) f2 s"] Xo1
      by(auto simp add: fst_l_def)

    then show "x <[ s2_1"
      using is_supD1[OF Sup2 Xin] using S2
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l2 f2 s ` V') w"

    have Ub' : "is_ub (LMap (fst_l l2) f2 s ` V) (w, s2_2)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (fst_l l2) f2 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (fst_l l2) f2 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo1 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (LMap l2 f2 s zo1, zo2)"
        using Zo
        by(auto simp add: fst_l_def)

      have Conc1 : "LMap l2 f2 s zo1 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo2 <[ s2_2"
        using is_supD1[OF Sup2 Zin] Zo_12 S2 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (w, s2_2)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed

    
    show "s2_1 <[ w"
      using is_supD2[OF Sup2 Ub'] S2
      by(auto simp add: prod_pleq)
  qed

  have Sin1' : "s1_1 \<in> S1 s \<inter> S2 s"
    using Sin1 S1
    by(auto simp add: fst_l_S_def)

  have Sin2' : "s2_1 \<in> S1 s \<inter> S2 s"
    using Sin2 S2
    by(auto simp add: fst_l_S_def)

  have Sup3 :  "is_sup (LMap l1 f1 s ` LMap l2 f2 s ` V') (LMap l1 f1 s s2_1)"
    using compat_pres1[OF V'(1) V'sub1 V'sub2 Sup'1 Sin1' Sup'2 Sin2']
    by auto

  show "is_sup (LMap (fst_l l1) f1 s ` LMap (fst_l l2) f2 s ` V)
        (LMap (fst_l l1) f1 s s2)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (fst_l l1) f1 s ` LMap (fst_l l2) f2 s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (fst_l l1) f1 s ( LMap (fst_l l2) f2 s xo) = x"
      by auto

    then obtain xo1 xo2 where Xo_12 : "xo = (xo1, xo2)" "xo1 \<in> V'"
      using SV'
      by(cases xo; auto)

    have Mapped : "LMap l1 f1 s (LMap l2 f2 s xo1) \<in> (LMap l1 f1 s ` LMap l2 f2 s ` V')"
      using imageI[OF Xo_12(2), of "LMap l1 f1 s o LMap l2 f2 s"]
      by auto

    have Leq1 : "LMap l1 f1 s (LMap l2 f2 s xo1) <[ (LMap l1 f1 s s2_1)"
      using is_supD1[OF Sup3 Mapped]
      by auto

    have X_eq : "x = (LMap l1 f1 s (LMap l2 f2 s xo1), xo2)"
      using Xo Xo_12
      by(auto simp add: fst_l_def)

    have Leq2 : "xo2 <[ s2_2"
      using is_supD1[OF Sup2 imageI, of xo] Xo Xo_12 S2
      by(auto simp add: prod_pleq fst_l_def)

    show "x <[ LMap (fst_l l1) f1 s s2"
      using Leq1 Leq2 X_eq S2
      by(auto simp add: prod_pleq fst_l_def)
  next
    fix w

    assume Ub: "is_ub (LMap (fst_l l1) f1 s ` LMap (fst_l l2) f2 s ` V) w"

    obtain w1 w2 where W: "w = (w1, w2)"
      by(cases w; auto)

    have Ub'1 : "is_ub (LMap l1 f1 s ` LMap l2 f2 s ` V') w1"
    proof(rule is_ubI)
      fix z

      assume Z: "z \<in> LMap l1 f1 s ` LMap l2 f2 s ` V'"

      obtain zo where Zo : "zo \<in> V'" "LMap l1 f1 s (LMap l2 f2 s zo) = z"
        using Z by auto

      then obtain z2 where Z2 : "(zo, z2) \<in> V"
        using SV' by auto

      then have "LMap (fst_l l1) f1 s (LMap (fst_l l2) f2 s (zo, z2)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(zo, z2)"]
        by auto

      then show "z <[ w1"
        using W Zo
        by(auto simp add: fst_l_def prod_pleq)
    qed

    have Conc1 : "(LMap l1 f1 s s2_1) <[ w1"
      using is_supD2[OF Sup3 Ub'1] by auto

    have Ub'2 : "is_ub (snd ` V) w2"
    proof(rule is_ubI)
      fix z
      assume Z : "z \<in> snd ` V"

      then obtain z1 where Z1 : "(z1, z) \<in> V"
        by auto

      then have "LMap (fst_l l1) f1 s (LMap (fst_l l2) f2 s (z1, z)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(z1, z)"]
        by auto

      then show "z <[ w2"
        using W
        by(auto simp add: fst_l_def prod_pleq)
    qed

    have Sup_snd : "is_sup (snd ` V) s2_2"
    proof(rule is_supI)

      fix k

      assume K: "k \<in> snd ` V"

      then obtain k1 where K1 : "(k1, k) \<in> V"
        by auto

      then show "k <[ s2_2"
        using is_supD1[OF Sup2 imageI, of "(k1, k)"] S2
        by(auto simp add: fst_l_def prod_pleq)
    next

      fix l

      assume L : "is_ub (snd ` V) l"

      have L' : "is_ub (LMap (fst_l l2) f2 s ` V) (s2_1, l)"
      proof(rule is_ubI)
        fix z

        assume Z: "z \<in> LMap (fst_l l2) f2 s ` V"

        then obtain z1 z2 where Z12 : "z = (z1, z2)"
          by(cases z; auto)

        then have Conc1 : "z1 <[ s2_1"
          using is_supD1[OF Sup2 Z] Z S2
          by(auto simp add: prod_pleq)

        obtain zo where Zo : "zo \<in> V" "LMap (fst_l l2) f2 s zo = z"
          using Z by auto

        obtain zo1 zo2 where Zo12 : "zo = (zo1, zo2)"
          by(cases zo; auto)

        have Zo2_eq : "zo2 = z2"
          using Z12 Zo12 Zo
          by(auto simp add: fst_l_def)

        have Z2_in : "z2 \<in> snd ` V"
          using imageI[OF Zo(1), of snd] Zo12 Zo2_eq
          by(auto)

        have Conc2 : "z2 <[ l"
          using is_ubE[OF L Z2_in]
          by(auto)

        then show "z <[ (s2_1, l)"
          using Z12 Conc1 Conc2
          by(auto simp add: prod_pleq)
      qed

      show "s2_2 <[ l"
        using is_supD2[OF Sup2 L'] S2
        by(auto simp add: prod_pleq)
    qed

    have "s2_2 <[ w2"
      using is_supD2[OF Sup_snd Ub'2]
      by auto

    then show "LMap (fst_l l1) f1 s s2 <[ w"
      using W S2 Conc1
      by(auto simp add: fst_l_def prod_pleq)
  qed
next
  fix s f1 f2 s1 s2 v 
  fix V :: "('c * 'g) set"

  assume Sup1 : "is_sup (LMap (fst_l l1) f1 s ` V) s1"
  assume Sup2 : "is_sup (LMap (fst_l l2) f2 s ` V) s2"
  assume Vin : "v \<in> V"
  assume Vsub1 : "V \<subseteq> fst_l_S S1 s"
  assume Vsub2 : "V \<subseteq> fst_l_S S2 s"

  assume Sin1 : "s1 \<in> fst_l_S S1 s \<inter> fst_l_S S2 s"
  assume Sin2 : "s2 \<in> fst_l_S S1 s \<inter> fst_l_S S2 s"

  obtain V' where SV' : "V' = { x1 . \<exists> x2 . (x1, x2) \<in> V}"
    by auto

  have V'sub1 : "V' \<subseteq> S1 s"
    using SV' Vsub1
    by(auto simp add: fst_l_S_def)

  have V'sub2 : "V' \<subseteq> S2 s"
    using SV' Vsub2
    by(auto simp add: fst_l_S_def)

  obtain v1 v2 where V' :
    "v1 \<in> V'" "v = (v1, v2)"
    using Vin
    unfolding SV'
    by (cases v; auto)

  obtain s1_1 s1_2 where S1 : "s1 = (s1_1, s1_2)"
    by(cases s1; auto)

  obtain s2_1 s2_2 where S2: "s2 = (s2_1, s2_2)"
    by(cases s2; auto)

  have Sup'1 : "is_sup (LMap l1 f1 s ` V') s1_1"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l1 f1 s ` V'"

    then obtain xo1 where Xo1 : "xo1 \<in> V'" "LMap l1 f1 s xo1 = x"
      by auto

    then obtain xo2 where Xo2 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(x, xo2) \<in> LMap (fst_l l1) f1 s ` V"
      using imageI[OF Xo2, of "LMap (fst_l l1) f1 s"] Xo1
      by(auto simp add: fst_l_def)

    then show "x <[ s1_1"
      using is_supD1[OF Sup1 Xin] using S1
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l1 f1 s ` V') w"

    have Ub' : "is_ub (LMap (fst_l l1) f1 s ` V) (w, s1_2)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (fst_l l1) f1 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (fst_l l1) f1 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo1 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (LMap l1 f1 s zo1, zo2)"
        using Zo
        by(auto simp add: fst_l_def)

      have Conc1 : "LMap l1 f1 s zo1 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo2 <[ s1_2"
        using is_supD1[OF Sup1 Zin] Zo_12 S1 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (w, s1_2)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed

    
    show "s1_1 <[ w"
      using is_supD2[OF Sup1 Ub'] S1
      by(auto simp add: prod_pleq)
  qed

  have Sup'2 : "is_sup (LMap l2 f2 s ` V') s2_1"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l2 f2 s ` V'"

    then obtain xo1 where Xo1 : "xo1 \<in> V'" "LMap l2 f2 s xo1 = x"
      by auto

    then obtain xo2 where Xo2 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(x, xo2) \<in> LMap (fst_l l2) f2 s ` V"
      using imageI[OF Xo2, of "LMap (fst_l l2) f2 s"] Xo1
      by(auto simp add: fst_l_def)

    then show "x <[ s2_1"
      using is_supD1[OF Sup2 Xin] using S2
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l2 f2 s ` V') w"

    have Ub' : "is_ub (LMap (fst_l l2) f2 s ` V) (w, s2_2)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (fst_l l2) f2 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (fst_l l2) f2 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo1 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (LMap l2 f2 s zo1, zo2)"
        using Zo
        by(auto simp add: fst_l_def)

      have Conc1 : "LMap l2 f2 s zo1 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo2 <[ s2_2"
        using is_supD1[OF Sup2 Zin] Zo_12 S2 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (w, s2_2)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed

    
    show "s2_1 <[ w"
      using is_supD2[OF Sup2 Ub'] S2
      by(auto simp add: prod_pleq)
  qed

  have Sin1' : "s1_1 \<in> S1 s \<inter> S2 s"
    using Sin1 S1
    by(auto simp add: fst_l_S_def)

  have Sin2' : "s2_1 \<in> S1 s \<inter> S2 s"
    using Sin2 S2
    by(auto simp add: fst_l_S_def)

  have Sup3 :  "is_sup (LMap l2 f2 s ` LMap l1 f1 s ` V') (LMap l2 f2 s s1_1)"
    using compat_pres2[OF V'(1) V'sub1 V'sub2 Sup'1 Sin1' Sup'2 Sin2']
    by auto

  show "is_sup (LMap (fst_l l2) f2 s ` LMap (fst_l l1) f1 s ` V)
        (LMap (fst_l l2) f2 s s1)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (fst_l l2) f2 s ` LMap (fst_l l1) f1 s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (fst_l l2) f2 s ( LMap (fst_l l1) f1 s xo) = x"
      by auto

    then obtain xo1 xo2 where Xo_12 : "xo = (xo1, xo2)" "xo1 \<in> V'"
      using SV'
      by(cases xo; auto)

    have Mapped : "LMap l2 f2 s (LMap l1 f1 s xo1) \<in> (LMap l2 f2 s ` LMap l1 f1 s ` V')"
      using imageI[OF Xo_12(2), of "LMap l2 f2 s o LMap l1 f1 s"]
      by auto

    have Leq1 : "LMap l2 f2 s (LMap l1 f1 s xo1) <[ (LMap l2 f2 s s1_1)"
      using is_supD1[OF Sup3 Mapped]
      by auto

    have X_eq : "x = (LMap l2 f2 s (LMap l1 f1 s xo1), xo2)"
      using Xo Xo_12
      by(auto simp add: fst_l_def)

    have Leq2 : "xo2 <[ s1_2"
      using is_supD1[OF Sup1 imageI, of xo] Xo Xo_12 S2 S1
      by(auto simp add: prod_pleq fst_l_def)

    show "x <[ LMap (fst_l l2) f2 s s1"
      using Leq1 Leq2 X_eq S2 S1
      by(auto simp add: prod_pleq fst_l_def)
  next
    fix w

    assume Ub: "is_ub (LMap (fst_l l2) f2 s ` LMap (fst_l l1) f1 s ` V) w"

    obtain w1 w2 where W: "w = (w1, w2)"
      by(cases w; auto)

    have Ub'1 : "is_ub (LMap l2 f2 s ` LMap l1 f1 s ` V') w1"
    proof(rule is_ubI)
      fix z

      assume Z: "z \<in> LMap l2 f2 s ` LMap l1 f1 s ` V'"

      obtain zo where Zo : "zo \<in> V'" "LMap l2 f2 s (LMap l1 f1 s zo) = z"
        using Z by auto

      then obtain z2 where Z2 : "(zo, z2) \<in> V"
        using SV' by auto

      then have "LMap (fst_l l2) f2 s (LMap (fst_l l1) f1 s (zo, z2)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(zo, z2)"]
        by auto

      then show "z <[ w1"
        using W Zo
        by(auto simp add: fst_l_def prod_pleq)
    qed

    have Conc1 : "(LMap l2 f2 s s1_1) <[ w1"
      using is_supD2[OF Sup3 Ub'1] by auto

    have Ub'2 : "is_ub (snd ` V) w2"
    proof(rule is_ubI)
      fix z
      assume Z : "z \<in> snd ` V"

      then obtain z1 where Z1 : "(z1, z) \<in> V"
        by auto

      then have "LMap (fst_l l2) f2 s (LMap (fst_l l1) f1 s (z1, z)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(z1, z)"]
        by auto

      then show "z <[ w2"
        using W
        by(auto simp add: fst_l_def prod_pleq)
    qed

    have Sup_snd : "is_sup (snd ` V) s1_2"
    proof(rule is_supI)

      fix k

      assume K: "k \<in> snd ` V"

      then obtain k1 where K1 : "(k1, k) \<in> V"
        by auto

      then show "k <[ s1_2"
        using is_supD1[OF Sup1 imageI, of "(k1, k)"] S1
        by(auto simp add: fst_l_def prod_pleq)
    next

      fix l

      assume L : "is_ub (snd ` V) l"

      have L' : "is_ub (LMap (fst_l l1) f1 s ` V) (s1_1, l)"
      proof(rule is_ubI)
        fix z

        assume Z: "z \<in> LMap (fst_l l1) f1 s ` V"

        then obtain z1 z2 where Z12 : "z = (z1, z2)"
          by(cases z; auto)

        then have Conc1 : "z1 <[ s1_1"
          using is_supD1[OF Sup1 Z] Z S1
          by(auto simp add: prod_pleq)

        obtain zo where Zo : "zo \<in> V" "LMap (fst_l l1) f1 s zo = z"
          using Z by auto

        obtain zo1 zo2 where Zo12 : "zo = (zo1, zo2)"
          by(cases zo; auto)

        have Zo2_eq : "zo2 = z2"
          using Z12 Zo12 Zo
          by(auto simp add: fst_l_def)

        have Z2_in : "z2 \<in> snd ` V"
          using imageI[OF Zo(1), of snd] Zo12 Zo2_eq
          by(auto)

        have Conc2 : "z2 <[ l"
          using is_ubE[OF L Z2_in]
          by(auto)

        then show "z <[ (s1_1, l)"
          using Z12 Conc1 Conc2
          by(auto simp add: prod_pleq)
      qed

      show "s1_2 <[ l"
        using is_supD2[OF Sup1 L'] S1
        by(auto simp add: prod_pleq)
    qed

    have "s1_2 <[ w2"
      using is_supD2[OF Sup_snd Ub'2]
      using is_supD2[OF Sup_snd ]
      by auto

    then show "LMap (fst_l l2) f2 s s1 <[ w"
      using W S2 Conc1 S1
      by(auto simp add: fst_l_def prod_pleq)
  qed
next
  fix a1 a2 s 
  fix x :: "('c * 'g)"

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

  have Compat1 : "LUpd l1 s a1 (LUpd l2 s a2 b2) = LUpd l2 s a2 (LUpd l1 s a1 b2)"
    using compat[of s a1 a2 b2]
    by(auto)

  then show "LUpd (snd_l l1) s a1 (LUpd (snd_l l2) s a2 b) =
       LUpd (snd_l l2) s a2 (LUpd (snd_l l1) s a1 b)"
    using B
    by(auto simp add: snd_l_def)
next

  fix b :: "('g * 'c)"
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
  fix b :: "('g * 'c)"
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
  fix b :: "'g * 'c"
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
  fix b :: "'g * 'c"
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
  fix s f1 f2 s1 s2 v 
  fix V :: "('g * 'c) set"

  assume Sup1 : "is_sup (LMap (snd_l l1) f1 s ` V) s1"
  assume Sup2 : "is_sup (LMap (snd_l l2) f2 s ` V) s2"
  assume Vin : "v \<in> V"
  assume Vsub1 : "V \<subseteq> snd_l_S S1 s"
  assume Vsub2 : "V \<subseteq> snd_l_S S2 s"

  assume Sin1 : "s1 \<in> snd_l_S S1 s \<inter> snd_l_S S2 s"
  assume Sin2 : "s2 \<in> snd_l_S S1 s \<inter> snd_l_S S2 s"

  obtain V' where SV' : "V' = { x2 . \<exists> x1 . (x1, x2) \<in> V}"
    by auto

  have V'sub1 : "V' \<subseteq> S1 s"
    using SV' Vsub1
    by(auto simp add: snd_l_S_def)

  have V'sub2 : "V' \<subseteq> S2 s"
    using SV' Vsub2
    by(auto simp add: snd_l_S_def)

  obtain v1 v2 where V' :
    "v2 \<in> V'" "v = (v1, v2)"
    using Vin
    unfolding SV'
    by (cases v; auto)

  obtain s1_1 s1_2 where S1 : "s1 = (s1_1, s1_2)"
    by(cases s1; auto)

  obtain s2_1 s2_2 where S2: "s2 = (s2_1, s2_2)"
    by(cases s2; auto)

  have Sup'1 : "is_sup (LMap l1 f1 s ` V') s1_2"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l1 f1 s ` V'"

    then obtain xo2 where Xo2 : "xo2 \<in> V'" "LMap l1 f1 s xo2 = x"
      by auto

    then obtain xo1 where Xo1 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(xo1, x) \<in> LMap (snd_l l1) f1 s ` V"
      using imageI[OF Xo1, of "LMap (snd_l l1) f1 s"] Xo2
      by(auto simp add: snd_l_def)

    then show "x <[ s1_2"
      using is_supD1[OF Sup1 Xin] using S1
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l1 f1 s ` V') w"

    have Ub' : "is_ub (LMap (snd_l l1) f1 s ` V) (s1_1, w)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (snd_l l1) f1 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (snd_l l1) f1 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo2 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (zo1, LMap l1 f1 s zo2)"
        using Zo
        by(auto simp add: snd_l_def)

      have Conc1 : "LMap l1 f1 s zo2 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo1 <[ s1_1"
        using is_supD1[OF Sup1 Zin] Zo_12 S1 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (s1_1, w)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed
    
    show "s1_2 <[ w"
      using is_supD2[OF Sup1 Ub'] S1
      by(auto simp add: prod_pleq)
  qed

  have Sup'2 : "is_sup (LMap l2 f2 s ` V') s2_2"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l2 f2 s ` V'"

    then obtain xo2 where Xo2 : "xo2 \<in> V'" "LMap l2 f2 s xo2 = x"
      by auto

    then obtain xo1 where Xo1 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(xo1, x) \<in> LMap (snd_l l2) f2 s ` V"
      using imageI[OF Xo1, of "LMap (snd_l l2) f2 s"] Xo2
      by(auto simp add: snd_l_def)

    then show "x <[ s2_2"
      using is_supD1[OF Sup2 Xin] using S2
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l2 f2 s ` V') w"

    have Ub' : "is_ub (LMap (snd_l l2) f2 s ` V) (s2_1, w)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (snd_l l2) f2 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (snd_l l2) f2 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo2 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (zo1, LMap l2 f2 s zo2)"
        using Zo
        by(auto simp add: snd_l_def)

      have Conc1 : "LMap l2 f2 s zo2 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo1 <[ s2_1"
        using is_supD1[OF Sup2 Zin] Zo_12 S2 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (s2_1, w)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed

    show "s2_2 <[ w"
      using is_supD2[OF Sup2 Ub'] S2
      by(auto simp add: prod_pleq)
  qed


  have Sin1' : "s1_2 \<in> S1 s \<inter> S2 s"
    using Sin1 S1
    by(auto simp add: snd_l_S_def)

  have Sin2' : "s2_2 \<in> S1 s \<inter> S2 s"
    using Sin2 S2
    by(auto simp add: snd_l_S_def)

  have Sup3 :  "is_sup (LMap l1 f1 s ` LMap l2 f2 s ` V') (LMap l1 f1 s s2_2)"
    using compat_pres1[OF V'(1) V'sub1 V'sub2 Sup'1 Sin1' Sup'2 Sin2']
    by auto

  show "is_sup (LMap (snd_l l1) f1 s ` LMap (snd_l l2) f2 s ` V)
        (LMap (snd_l l1) f1 s s2)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (snd_l l1) f1 s ` LMap (snd_l l2) f2 s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (snd_l l1) f1 s ( LMap (snd_l l2) f2 s xo) = x"
      by auto

    then obtain xo1 xo2 where Xo_12 : "xo = (xo1, xo2)" "xo2 \<in> V'"
      using SV'
      by(cases xo; auto)

    have Mapped : "LMap l1 f1 s (LMap l2 f2 s xo2) \<in> (LMap l1 f1 s ` LMap l2 f2 s ` V')"
      using imageI[OF Xo_12(2), of "LMap l1 f1 s o LMap l2 f2 s"]
      by auto

    have Leq1 : "LMap l1 f1 s (LMap l2 f2 s xo2) <[ (LMap l1 f1 s s2_2)"
      using is_supD1[OF Sup3 Mapped]
      by auto

    have X_eq : "x = (xo1, LMap l1 f1 s (LMap l2 f2 s xo2))"
      using Xo Xo_12
      by(auto simp add: snd_l_def)

    have Leq2 : "xo1 <[ s2_1"
      using is_supD1[OF Sup2 imageI, of xo] Xo Xo_12 S2
      by(auto simp add: prod_pleq snd_l_def)

    show "x <[ LMap (snd_l l1) f1 s s2"
      using Leq1 Leq2 X_eq S2
      by(auto simp add: prod_pleq snd_l_def)
  next
    fix w

    assume Ub: "is_ub (LMap (snd_l l1) f1 s ` LMap (snd_l l2) f2 s ` V) w"

    obtain w1 w2 where W: "w = (w1, w2)"
      by(cases w; auto)

    have Ub'1 : "is_ub (LMap l1 f1 s ` LMap l2 f2 s ` V') w2"
    proof(rule is_ubI)
      fix z

      assume Z: "z \<in> LMap l1 f1 s ` LMap l2 f2 s ` V'"

      obtain zo where Zo : "zo \<in> V'" "LMap l1 f1 s (LMap l2 f2 s zo) = z"
        using Z by auto

      then obtain z1 where Z1 : "(z1, zo) \<in> V"
        using SV' by auto

      then have "LMap (snd_l l1) f1 s (LMap (snd_l l2) f2 s (z1, zo)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(z1, zo)"]
        by auto

      then show "z <[ w2"
        using W Zo
        by(auto simp add: snd_l_def prod_pleq)
    qed

    have Conc1 : "(LMap l1 f1 s s2_2) <[ w2"
      using is_supD2[OF Sup3 Ub'1] by auto

    have Ub'2 : "is_ub (fst ` V) w1"
    proof(rule is_ubI)
      fix z
      assume Z : "z \<in> fst ` V"

      then obtain z2 where Z2 : "(z, z2) \<in> V"
        by auto

      then have "LMap (snd_l l1) f1 s (LMap (snd_l l2) f2 s (z, z2)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(z, z2)"]
        by auto

      then show "z <[ w1"
        using W
        by(auto simp add: snd_l_def prod_pleq)
    qed

    have Sup_fst : "is_sup (fst ` V) s2_1"
    proof(rule is_supI)

      fix k

      assume K: "k \<in> fst ` V"

      then obtain k2 where K2 : "(k, k2) \<in> V"
        by auto

      then show "k <[ s2_1"
        using is_supD1[OF Sup2 imageI, of "(k, k2)"] S2
        by(auto simp add: snd_l_def prod_pleq)
    next

      fix l

      assume L : "is_ub (fst ` V) l"

      have L' : "is_ub (LMap (snd_l l2) f2 s ` V) (l, s2_2)"
      proof(rule is_ubI)
        fix z

        assume Z: "z \<in> LMap (snd_l l2) f2 s ` V"

        then obtain z1 z2 where Z12 : "z = (z1, z2)"
          by(cases z; auto)

        then have Conc1 : "z2 <[ s2_2"
          using is_supD1[OF Sup2 Z] Z S2
          by(auto simp add: prod_pleq)

        obtain zo where Zo : "zo \<in> V" "LMap (snd_l l2) f2 s zo = z"
          using Z by auto

        obtain zo1 zo2 where Zo12 : "zo = (zo1, zo2)"
          by(cases zo; auto)

        have Zo1_eq : "zo1 = z1"
          using Z12 Zo12 Zo
          by(auto simp add: snd_l_def)

        have Z1_in : "z1 \<in> fst ` V"
          using imageI[OF Zo(1), of fst] Zo12 Zo1_eq
          by(auto)

        have Conc2 : "z1 <[ l"
          using is_ubE[OF L Z1_in]
          by(auto)

        then show "z <[ (l, s2_2)"
          using Z12 Conc1 Conc2
          by(auto simp add: prod_pleq)
      qed

      show "s2_1 <[ l"
        using is_supD2[OF Sup2 L'] S2
        by(auto simp add: prod_pleq)
    qed

    have "s2_1 <[ w1"
      using is_supD2[OF Sup_fst Ub'2]
      by auto

    then show "LMap (snd_l l1) f1 s s2 <[ w"
      using W S2 Conc1
      by(auto simp add: snd_l_def prod_pleq)
  qed
next
  fix s f1 f2 s1 s2 v 
  fix V :: "('g * 'c) set"

  assume Sup1 : "is_sup (LMap (snd_l l1) f1 s ` V) s1"
  assume Sup2 : "is_sup (LMap (snd_l l2) f2 s ` V) s2"
  assume Vin : "v \<in> V"
  assume Vsub1 : "V \<subseteq> snd_l_S S1 s"
  assume Vsub2 : "V \<subseteq> snd_l_S S2 s"

  assume Sin1 : "s1 \<in> snd_l_S S1 s \<inter> snd_l_S S2 s"
  assume Sin2 : "s2 \<in> snd_l_S S1 s \<inter> snd_l_S S2 s"

  obtain V' where SV' : "V' = { x2 . \<exists> x1 . (x1, x2) \<in> V}"
    by auto

  have V'sub1 : "V' \<subseteq> S1 s"
    using SV' Vsub1
    by(auto simp add: snd_l_S_def)

  have V'sub2 : "V' \<subseteq> S2 s"
    using SV' Vsub2
    by(auto simp add: snd_l_S_def)

  obtain v1 v2 where V' :
    "v2 \<in> V'" "v = (v1, v2)"
    using Vin
    unfolding SV'
    by (cases v; auto)

  obtain s1_1 s1_2 where S1 : "s1 = (s1_1, s1_2)"
    by(cases s1; auto)

  obtain s2_1 s2_2 where S2: "s2 = (s2_1, s2_2)"
    by(cases s2; auto)

  have Sup'1 : "is_sup (LMap l1 f1 s ` V') s1_2"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l1 f1 s ` V'"

    then obtain xo2 where Xo2 : "xo2 \<in> V'" "LMap l1 f1 s xo2 = x"
      by auto

    then obtain xo1 where Xo1 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(xo1, x) \<in> LMap (snd_l l1) f1 s ` V"
      using imageI[OF Xo1, of "LMap (snd_l l1) f1 s"] Xo2
      by(auto simp add: snd_l_def)

    then show "x <[ s1_2"
      using is_supD1[OF Sup1 Xin] using S1
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l1 f1 s ` V') w"

    have Ub' : "is_ub (LMap (snd_l l1) f1 s ` V) (s1_1, w)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (snd_l l1) f1 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (snd_l l1) f1 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo2 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (zo1, LMap l1 f1 s zo2)"
        using Zo
        by(auto simp add: snd_l_def)

      have Conc1 : "LMap l1 f1 s zo2 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo1 <[ s1_1"
        using is_supD1[OF Sup1 Zin] Zo_12 S1 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (s1_1, w)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed
    
    show "s1_2 <[ w"
      using is_supD2[OF Sup1 Ub'] S1
      by(auto simp add: prod_pleq)
  qed

  have Sup'2 : "is_sup (LMap l2 f2 s ` V') s2_2"
  proof(rule is_supI)
    fix x
    assume X: "x \<in> LMap l2 f2 s ` V'"

    then obtain xo2 where Xo2 : "xo2 \<in> V'" "LMap l2 f2 s xo2 = x"
      by auto

    then obtain xo1 where Xo1 : "(xo1, xo2) \<in> V"
      using SV' by auto

    then have Xin : "(xo1, x) \<in> LMap (snd_l l2) f2 s ` V"
      using imageI[OF Xo1, of "LMap (snd_l l2) f2 s"] Xo2
      by(auto simp add: snd_l_def)

    then show "x <[ s2_2"
      using is_supD1[OF Sup2 Xin] using S2
      by(auto simp add: prod_pleq)
  next

    fix w

    assume Ub : "is_ub (LMap l2 f2 s ` V') w"

    have Ub' : "is_ub (LMap (snd_l l2) f2 s ` V) (s2_1, w)"
    proof(rule is_ubI)
      fix z
      assume Zin: "z \<in> LMap (snd_l l2) f2 s ` V"

      obtain zo where Zo : "zo \<in> V" "LMap (snd_l l2) f2 s zo = z"
        using Zin by auto

      obtain zo1 zo2 where Zo_12 : "zo = (zo1, zo2)" "zo2 \<in> V'"
        using Zo(1) SV'
        by(cases zo; auto)

      then have Z_eq : "z = (zo1, LMap l2 f2 s zo2)"
        using Zo
        by(auto simp add: snd_l_def)

      have Conc1 : "LMap l2 f2 s zo2 <[ w"
        using is_ubE[OF Ub imageI] Zo_12
        by auto

      have Conc2 : "zo1 <[ s2_1"
        using is_supD1[OF Sup2 Zin] Zo_12 S2 Z_eq
        by(auto simp add: prod_pleq)

      then show "z <[ (s2_1, w)"
        using Z_eq Conc1 Conc2
        by(auto simp add: prod_pleq)
    qed

    show "s2_2 <[ w"
      using is_supD2[OF Sup2 Ub'] S2
      by(auto simp add: prod_pleq)
  qed


  have Sin1' : "s1_2 \<in> S1 s \<inter> S2 s"
    using Sin1 S1
    by(auto simp add: snd_l_S_def)

  have Sin2' : "s2_2 \<in> S1 s \<inter> S2 s"
    using Sin2 S2
    by(auto simp add: snd_l_S_def)

  have Sup3 :  "is_sup (LMap l2 f2 s ` LMap l1 f1 s ` V') (LMap l2 f2 s s1_2)"
    using compat_pres2[OF V'(1) V'sub1 V'sub2 Sup'1 Sin1' Sup'2 Sin2']
    by auto

  show "is_sup (LMap (snd_l l2) f2 s ` LMap (snd_l l1) f1 s ` V)
        (LMap (snd_l l2) f2 s s1)"
  proof(rule is_supI)
    fix x

    assume X : "x \<in> LMap (snd_l l2) f2 s ` LMap (snd_l l1) f1 s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (snd_l l2) f2 s ( LMap (snd_l l1) f1 s xo) = x"
      by auto

    then obtain xo1 xo2 where Xo_12 : "xo = (xo1, xo2)" "xo2 \<in> V'"
      using SV'
      by(cases xo; auto)

    have Mapped : "LMap l2 f2 s (LMap l1 f1 s xo2) \<in> (LMap l2 f2 s ` LMap l1 f1 s ` V')"
      using imageI[OF Xo_12(2), of "LMap l2 f2 s o LMap l1 f1 s"]
      by auto

    have Leq1 : "LMap l2 f2 s (LMap l1 f1 s xo2) <[ (LMap l2 f2 s s1_2)"
      using is_supD1[OF Sup3 Mapped]
      by auto

    have X_eq : "x = (xo1, LMap l2 f2 s (LMap l1 f1 s xo2))"
      using Xo Xo_12
      by(auto simp add: snd_l_def)

    have Leq2 : "xo1 <[ s1_1"
      using is_supD1[OF Sup1 imageI, of xo] Xo Xo_12 S2 S1
      by(auto simp add: prod_pleq snd_l_def)

    show "x <[ LMap (snd_l l2) f2 s s1"
      using Leq1 Leq2 X_eq S2 S1
      by(auto simp add: prod_pleq snd_l_def)
  next
    fix w

    assume Ub: "is_ub (LMap (snd_l l2) f2 s ` LMap (snd_l l1) f1 s ` V) w"

    obtain w1 w2 where W: "w = (w1, w2)"
      by(cases w; auto)

    have Ub'1 : "is_ub (LMap l2 f2 s ` LMap l1 f1 s ` V') w2"
    proof(rule is_ubI)
      fix z

      assume Z: "z \<in> LMap l2 f2 s ` LMap l1 f1 s ` V'"

      obtain zo where Zo : "zo \<in> V'" "LMap l2 f2 s (LMap l1 f1 s zo) = z"
        using Z by auto

      then obtain z1 where Z1 : "(z1, zo) \<in> V"
        using SV' by auto

      then have "LMap (snd_l l2) f2 s (LMap (snd_l l1) f1 s (z1, zo)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(z1, zo)"]
        by auto

      then show "z <[ w2"
        using W Zo
        by(auto simp add: snd_l_def prod_pleq)
    qed

    have Conc1 : "(LMap l2 f2 s s1_2) <[ w2"
      using is_supD2[OF Sup3 Ub'1] by auto

    have Ub'2 : "is_ub (fst ` V) w1"
    proof(rule is_ubI)
      fix z
      assume Z : "z \<in> fst ` V"

      then obtain z2 where Z1 : "(z, z2) \<in> V"
        by auto

      then have "LMap (snd_l l2) f2 s (LMap (snd_l l1) f1 s (z, z2)) <[ w"
        using is_ubE[OF Ub imageI[OF imageI], of "(z, z2)"]
        by auto

      then show "z <[ w1"
        using W
        by(auto simp add: snd_l_def prod_pleq)
    qed

    have Sup_snd : "is_sup (fst ` V) s1_1"
    proof(rule is_supI)

      fix k

      assume K: "k \<in> fst ` V"

      then obtain k2 where K1 : "(k, k2) \<in> V"
        by auto

      then show "k <[ s1_1"
        using is_supD1[OF Sup1 imageI, of "(k, k2)"] S1
        by(auto simp add: snd_l_def prod_pleq)
    next

      fix l

      assume L : "is_ub (fst ` V) l"

      have L' : "is_ub (LMap (snd_l l1) f1 s ` V) (l, s1_2)"
      proof(rule is_ubI)
        fix z

        assume Z: "z \<in> LMap (snd_l l1) f1 s ` V"

        then obtain z1 z2 where Z12 : "z = (z1, z2)"
          by(cases z; auto)

        then have Conc1 : "z2 <[ s1_2"
          using is_supD1[OF Sup1 Z] Z S1
          by(auto simp add: prod_pleq)

        obtain zo where Zo : "zo \<in> V" "LMap (snd_l l1) f1 s zo = z"
          using Z by auto

        obtain zo1 zo2 where Zo12 : "zo = (zo1, zo2)"
          by(cases zo; auto)

        have Zo2_eq : "zo1 = z1"
          using Z12 Zo12 Zo
          by(auto simp add: snd_l_def)

        have Z2_in : "z1 \<in> fst ` V"
          using imageI[OF Zo(1), of fst] Zo12 Zo2_eq
          by(auto)

        have Conc2 : "z1 <[ l"
          using is_ubE[OF L Z2_in]
          by(auto)

        then show "z <[ (l, s1_2)"
          using Z12 Conc1 Conc2
          by(auto simp add: prod_pleq)
      qed

      show "s1_1 <[ l"
        using is_supD2[OF Sup1 L'] S1
        by(auto simp add: prod_pleq)
    qed

    have "s1_1 <[ w1"
      using is_supD2[OF Sup_snd Ub'2]
      by auto

    then show "LMap (snd_l l2) f2 s s1 <[ w"
      using W S2 Conc1 S1
      by(auto simp add: snd_l_def prod_pleq)
  qed
next
  fix a1 a2 s
  fix x :: "'g * 'c"
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

(*
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
*)
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

  then show "LUpd (fst_l l1) s a1 (LUpd (snd_l l2) s a2 b) = LUpd (snd_l l2) s a2 (LUpd (fst_l l1) s a1 b)"
    by(auto simp add: fst_l_def snd_l_def)

next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LOut (snd_l l2) s (LUpd (fst_l l1) s a1 b) = LOut (snd_l l2) s b"
    by(auto simp add: fst_l_def snd_l_def)
next

  fix b :: "'c * 'f"
  fix s :: 'a
  fix a2 :: 'e


  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show "LOut (fst_l l1) s (LUpd (snd_l l2) s a2 b) = LOut (fst_l l1) s b"
    by(cases b; auto simp add: fst_l_def snd_l_def)


next
  fix b :: "'c * 'f"
  fix s :: 'a
  fix a1 :: 'b

  assume Bin : "b \<in> snd_l_S S2 s"

  obtain b1 b2 where B: "b = (b1, b2)"
    by(cases b; auto)

  then show " LUpd (fst_l l1) s a1 b \<in> snd_l_S S2 s" using Bin
    by(auto simp add: fst_l_def snd_l_S_def)
next
  fix b :: "'c * 'f"
  fix s :: 'a
  fix a2 :: 'e

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
  fix s f1 f2 s1 s2 v
  fix V :: "('c * 'f) set"

  assume Vin: "v \<in> V"
  assume Vsub1 : "V \<subseteq> fst_l_S S1 s"
  assume Vsub2 : "V \<subseteq> snd_l_S S2 s"
  assume Sup1 : "is_sup (LMap (fst_l l1) f1 s ` V) s1"
  assume Sup2 : "is_sup (LMap (snd_l l2) f2 s ` V) s2"

  assume Sin1 : "s1 \<in> fst_l_S S1 s \<inter> snd_l_S S2 s"
  assume Sin2 : "s2 \<in> fst_l_S S1 s \<inter> snd_l_S S2 s"

  obtain s1_1 s1_2 where S1 : "s1 = (s1_1, s1_2)"
    by(cases s1; auto)

  obtain s2_1 s2_2 where S2 : "s2 = (s2_1, s2_2)"
    by(cases s2; auto)

  obtain v1 v2 where V: "v = (v1, v2)"
    by(cases v; auto)

  have V1in : "v1 \<in> (fst ` V)"
    using imageI[OF Vin, of fst] V
    by auto

  have V1sub : "fst ` V \<subseteq> S1 s"
    using V1in Vsub1
    by(auto simp add: fst_l_S_def)

  have V2in : "v2 \<in> snd ` V"
    using imageI[OF Vin, of snd] V
    by auto

  have V2sub : "snd ` V \<subseteq> S2 s"
    using V2in Vsub2
    by(auto simp add: snd_l_S_def)

  have "\<And> x . fst (LMap (snd_l l2) f2 s x) = fst x"
  proof-
    fix x
    show "fst (LMap (snd_l l2) f2 s x) = fst x"
      by(cases x; auto simp add: snd_l_def)
  qed

  then have Fst_eq : "(fst \<circ> LMap (snd_l l2) f2 s) = fst"
    using HOL.ext
    by(fastforce)

  then have Fst_v_eq : "fst ` LMap (snd_l l2) f2 s ` V = fst ` V" 
    unfolding image_comp Fst_eq
    by simp

  have "\<And> x . snd (LMap (fst_l l1) f1 s x) = snd x"
  proof-
    fix x
    show "snd (LMap (fst_l l1) f1 s x) = snd x"
      by(cases x; auto simp add: fst_l_def)
  qed

  then have Snd_eq : "(snd \<circ> LMap (fst_l l1) f1 s) = snd"
    using HOL.ext
    by(fastforce)

  then have Snd_v_eq : "snd ` LMap (fst_l l1) f1 s ` V = snd ` V" 
    unfolding image_comp Snd_eq
    by simp

  have Fst_sup : "is_sup (fst ` V) s2_1"
    using is_sup_fst'[OF imageI[OF Vin] Sup2[unfolded S2]] unfolding Fst_v_eq
    by simp

  have Snd_sup : "is_sup (snd ` V) s1_2"
    using is_sup_snd'[OF imageI[OF Vin] Sup1[unfolded S1]] unfolding Snd_v_eq
    by simp

  have Sin'1 : "s2_1 \<in> S1 s"
    using Sin2 S2 
    by(auto simp add: fst_l_S_def)

  have So1_sup : "is_sup (LMap l1 f1 s ` fst ` V) (LMap l1 f1 s s2_1)"
    using in1.pres[OF V1in V1sub Fst_sup Sin'1]
    by auto

  have Sin'2 : "s1_2 \<in> S2 s"
    using Sin1 S1
    by(auto simp add: snd_l_S_def)

  have So2_sup : "is_sup (LMap l2 f2 s ` snd ` V) (LMap l2 f2 s s1_2)"
    using in2.pres[OF V2in V2sub Snd_sup Sin'2]
    by auto

  have S1_1_sup : "is_sup (LMap l1 f1 s ` fst ` V) (s1_1)"
  proof(rule is_supI)

    fix x

    assume X : "x \<in> LMap l1 f1 s ` fst ` V"

    then obtain xo where Xo: "xo \<in> V" "LMap l1 f1 s (fst xo) = x"
      unfolding image_comp by auto

    obtain xo1 xo2 where Xo12 : "xo = (xo1, xo2)"
      by(cases xo; auto)

    have In : "LMap (fst_l l1) f1 s xo \<in> LMap (fst_l l1) f1 s ` V"
      using imageI[OF Xo(1)]
      by auto


    show "x <[ s1_1"
      using is_supD1[OF Sup1 In] Xo Xo12 S1
      by(auto simp add: fst_l_def prod_pleq)
  next
    fix x'
    assume Ub : "is_ub (LMap l1 f1 s ` fst ` V) x'"

    have Ub' : "is_ub (LMap (fst_l l1) f1 s ` V) (x', s1_2)"
    proof(rule is_ubI)
      fix w

      assume W : "w \<in> LMap (fst_l l1) f1 s ` V"

      then obtain wo where Wo : "wo \<in> V" "LMap (fst_l l1) f1 s wo = w"
        by auto

      obtain w1 w2 where W12 : "w = (w1, w2)"
        by(cases w; auto)

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have W1' : "w1 = LMap l1 f1 s (fst wo)"
        using Wo W12 Wo12
        by(auto simp add: fst_l_def)

      have In1 : "w1 \<in> LMap l1 f1 s ` fst ` V"
        using imageI[OF Wo(1), of "LMap l1 f1 s o fst"] 
        unfolding image_comp W1'
        by auto

      have Conc1 : "w1 <[ x'"
        using is_ubE[OF Ub In1] by auto

      have W2: "w2 = wo2"
        using Wo W12 Wo12
        by(auto simp add: fst_l_def)

      then have In2 : "w2 \<in> snd ` V"
        using imageI[OF Wo(1), of snd] W12 Wo12
        by auto
        
      have Conc2 : "w2 <[ s1_2"
        using is_supD1[OF Snd_sup In2] by auto

      show "w <[ (x', s1_2)"
        using Conc1 Conc2 W12
        by (auto simp add: prod_pleq)
    qed

    show "s1_1 <[ x'"
      using is_supD2[OF Sup1 Ub'] S1
      by(auto simp add: prod_pleq)
  qed

  have S1_1_eq : "LMap l1 f1 s s2_1 = s1_1"
    using is_sup_unique[OF So1_sup S1_1_sup] by auto

  have S2_2_sup : "is_sup (LMap l2 f2 s ` snd ` V) (s2_2)"
  proof(rule is_supI)

    fix x

    assume X: "x \<in> LMap l2 f2 s ` snd ` V"

    obtain xo where Xo : "(xo \<in> V)" "LMap l2 f2 s (snd xo) = x"
      using X unfolding image_comp
      by auto

    have Xo_in' :  "LMap (snd_l l2) f2 s xo \<in> LMap (snd_l l2) f2 s ` V "
      using imageI[OF Xo(1)]
      by fastforce

    have Conc'1 : "LMap (snd_l l2) f2 s xo <[ s2"
      using is_supD1[OF Sup2 Xo_in']
      by auto

    obtain xo1 xo2 where Xo12 : "xo = (xo1, xo2)"
      by(cases xo; auto)

    show "x <[ s2_2"
      using Conc'1 Xo S2 Xo12
      by(auto simp add: snd_l_def prod_pleq)
  next
    fix x'

    assume Ub : "is_ub (LMap l2 f2 s ` snd ` V) x'"

    have Ub' : "is_ub (LMap (snd_l l2) f2 s ` V) (s2_1, x')"
    proof(rule is_ubI)
      fix w

      assume W : "w \<in> LMap (snd_l l2) f2 s ` V "

      then obtain wo where Wo : "wo \<in> V" "LMap (snd_l l2) f2 s wo = w"
        by auto

      obtain w1 w2 where W12 : "w = (w1, w2)"
        by(cases w; auto)

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have W2' : "w2 = LMap l2 f2 s (snd wo)"
        using Wo W12 Wo12
        by(auto simp add: snd_l_def)

      have In2 : "w2 \<in> LMap l2 f2 s ` snd ` V"
        using imageI[OF Wo(1), of "LMap l2 f2 s o snd"] 
        unfolding image_comp W2'
        by auto

      have Conc1 : "w2 <[ x'"
        using is_ubE[OF Ub In2] by auto

      have W1: "w1 = wo1"
        using Wo W12 Wo12
        by(auto simp add:snd_l_def)

      then have In1 : "w1 \<in> fst ` V"
        using imageI[OF Wo(1), of fst] W12 Wo12
        by auto
        
      have Conc2 : "w1 <[ s2_1"
        using is_supD1[OF Fst_sup In1] by auto

      show "w <[ (s2_1, x')"
        using Conc1 Conc2 W12
        by (auto simp add: prod_pleq)
    qed

    show "s2_2 <[ x'"
      using is_supD2[OF Sup2 Ub'] S2
      by(auto simp add: prod_pleq)
  qed

  show "is_sup (LMap (fst_l l1) f1 s ` LMap (snd_l l2) f2 s ` V) (LMap (fst_l l1) f1 s s2)"
  proof(rule is_supI)
    fix x

    assume X: "x \<in> LMap (fst_l l1) f1 s ` LMap (snd_l l2) f2 s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (fst_l l1) f1 s (LMap (snd_l l2) f2 s xo) = x"
      unfolding image_comp by auto

    obtain xo1 xo2 where Xo12 : "xo = (xo1, xo2)"
      by(cases xo; auto)

    obtain x1 x2 where X12 : "x = (x1, x2)"
      by(cases x; auto)

    have Eq1 : "x1 = LMap l1 f1 s xo1"
      using Xo Xo12 X12
      by(auto simp add: fst_l_def snd_l_def)

    have Xo1_in : "xo1 \<in> (fst ` V)"
      using imageI[OF Xo(1), of "fst"] Xo12 by auto

    have In1: "x1 \<in> LMap l1 f1 s ` fst ` V"
      using imageI[OF Xo1_in, of "LMap l1 f1 s "]
      unfolding image_comp Eq1
      by auto

    have Conc1 : "x1 <[ LMap l1 f1 s s2_1"
      using is_supD1[OF So1_sup In1]
      by auto

    have Eq2 : "x2 = LMap l2 f2 s xo2"
      using Xo Xo12 X12
      by(auto simp add: fst_l_def snd_l_def)

    have Xo2_in : "xo2 \<in> (snd ` V)"
      using imageI[OF Xo(1), of "snd"] Xo12 by auto

    have In2 : "x2 \<in> LMap l2 f2 s ` snd ` V"
      using imageI[OF Xo2_in, of "LMap l2 f2 s"]
      unfolding image_comp Eq2
      by auto

    have Conc2 : "x2 <[ s2_2"
      using is_supD1[OF S2_2_sup In2]
      by auto

    show "x <[ LMap (fst_l l1) f1 s s2" using S2 X12
      Conc1 Conc2
      by(auto simp add: fst_l_def prod_pleq)
  next
    fix x'

    assume Ub : "is_ub (LMap (fst_l l1) f1 s ` LMap (snd_l l2) f2 s ` V) x'"

    obtain x'1 x'2 where X'12 : "x' = (x'1, x'2)"
      by(cases x'; auto)

    have Eq: "LMap (fst_l l1) f1 s s2 = (s1_1, s2_2)"
      using S2 S1_1_eq
      by(auto simp add: fst_l_def)

    have Ub1 : "is_ub (LMap l1 f1 s ` fst ` V) x'1"
    proof(rule is_ubI)
      fix w
      assume W: "w \<in> LMap l1 f1 s ` fst ` V"

      then obtain wo where Wo : "wo \<in> V" "LMap l1 f1 s (fst wo) = w"
        unfolding image_comp by auto

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have In: "(LMap (fst_l l1) f1 s (LMap (snd_l l2) f2 s wo)) \<in> LMap (fst_l l1) f1 s ` LMap (snd_l l2) f2 s ` V "
        using imageI[OF Wo(1)] unfolding image_comp
        by auto

      have "(LMap (fst_l l1) f1 s (LMap (snd_l l2) f2 s wo)) = (w, LMap l2 f2 s wo2)"
        using Wo Wo12
        by(auto simp add: fst_l_def snd_l_def)

      then have "(w, LMap l2 f2 s wo2) <[ x'"
        using is_ubE[OF Ub In]
        by auto

      then show "w <[ x'1" using X'12
        by(auto simp add: prod_pleq)
    qed

    have Ub2 : "is_ub (LMap l2 f2 s ` snd ` V) x'2"
    proof(rule is_ubI)
      fix w
      assume W: "w \<in> LMap l2 f2 s ` snd ` V"

      then obtain wo where Wo : "wo \<in> V" "LMap l2 f2 s (snd wo) = w"
        unfolding image_comp by auto

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have In: "(LMap (fst_l l1) f1 s (LMap (snd_l l2) f2 s wo)) \<in> LMap (fst_l l1) f1 s ` LMap (snd_l l2) f2 s ` V "
        using imageI[OF Wo(1)] unfolding image_comp
        by auto

      have "(LMap (fst_l l1) f1 s (LMap (snd_l l2) f2 s wo)) = (LMap l1 f1 s wo1, w)"
        using Wo Wo12
        by(auto simp add: fst_l_def snd_l_def)

      then have "(LMap l1 f1 s wo1, w) <[ x'"
        using is_ubE[OF Ub In]
        by auto

      then show "w <[ x'2" using X'12
        by(auto simp add: prod_pleq)
    qed

    show "LMap (fst_l l1) f1 s s2 <[ x'"
      unfolding Eq X'12
      using is_supD2[OF S1_1_sup Ub1] is_supD2[OF S2_2_sup Ub2]
      by(auto simp add: prod_pleq)
  qed
next
  fix s f1 f2 s1 s2 v
  fix V :: "('c * 'f) set"

  assume Vin: "v \<in> V"
  assume Vsub1 : "V \<subseteq> fst_l_S S1 s"
  assume Vsub2 : "V \<subseteq> snd_l_S S2 s"
  assume Sup1 : "is_sup (LMap (fst_l l1) f1 s ` V) s1"
  assume Sup2 : "is_sup (LMap (snd_l l2) f2 s ` V) s2"

  assume Sin1 : "s1 \<in> fst_l_S S1 s \<inter> snd_l_S S2 s"
  assume Sin2 : "s2 \<in> fst_l_S S1 s \<inter> snd_l_S S2 s"

  obtain s1_1 s1_2 where S1 : "s1 = (s1_1, s1_2)"
    by(cases s1; auto)

  obtain s2_1 s2_2 where S2 : "s2 = (s2_1, s2_2)"
    by(cases s2; auto)

  obtain v1 v2 where V: "v = (v1, v2)"
    by(cases v; auto)

  have V1in : "v1 \<in> (fst ` V)"
    using imageI[OF Vin, of fst] V
    by auto

  have V1sub : "fst ` V \<subseteq> S1 s"
    using V1in Vsub1
    by(auto simp add: fst_l_S_def)

  have V2in : "v2 \<in> snd ` V"
    using imageI[OF Vin, of snd] V
    by auto

  have V2sub : "snd ` V \<subseteq> S2 s"
    using V2in Vsub2
    by(auto simp add: snd_l_S_def)

  have "\<And> x . fst (LMap (snd_l l2) f2 s x) = fst x"
  proof-
    fix x
    show "fst (LMap (snd_l l2) f2 s x) = fst x"
      by(cases x; auto simp add: snd_l_def)
  qed

  then have Fst_eq : "(fst \<circ> LMap (snd_l l2) f2 s) = fst"
    using HOL.ext
    by(fastforce)

  then have Fst_v_eq : "fst ` LMap (snd_l l2) f2 s ` V = fst ` V" 
    unfolding image_comp Fst_eq
    by simp

  have "\<And> x . snd (LMap (fst_l l1) f1 s x) = snd x"
  proof-
    fix x
    show "snd (LMap (fst_l l1) f1 s x) = snd x"
      by(cases x; auto simp add: fst_l_def)
  qed

  then have Snd_eq : "(snd \<circ> LMap (fst_l l1) f1 s) = snd"
    using HOL.ext
    by(fastforce)

  then have Snd_v_eq : "snd ` LMap (fst_l l1) f1 s ` V = snd ` V" 
    unfolding image_comp Snd_eq
    by simp

  have Fst_sup : "is_sup (fst ` V) s2_1"
    using is_sup_fst'[OF imageI[OF Vin] Sup2[unfolded S2]] unfolding Fst_v_eq
    by simp

  have Snd_sup : "is_sup (snd ` V) s1_2"
    using is_sup_snd'[OF imageI[OF Vin] Sup1[unfolded S1]] unfolding Snd_v_eq
    by simp

  have Sin'1 : "s2_1 \<in> S1 s"
    using Sin2 S2 
    by(auto simp add: fst_l_S_def)

  have So1_sup : "is_sup (LMap l1 f1 s ` fst ` V) (LMap l1 f1 s s2_1)"
    using in1.pres[OF V1in V1sub Fst_sup Sin'1]
    by auto

  have Sin'2 : "s1_2 \<in> S2 s"
    using Sin1 S1
    by(auto simp add: snd_l_S_def)

  have So2_sup : "is_sup (LMap l2 f2 s ` snd ` V) (LMap l2 f2 s s1_2)"
    using in2.pres[OF V2in V2sub Snd_sup Sin'2]
    by auto

  have S1_1_sup : "is_sup (LMap l1 f1 s ` fst ` V) (s1_1)"
  proof(rule is_supI)

    fix x

    assume X : "x \<in> LMap l1 f1 s ` fst ` V"

    then obtain xo where Xo: "xo \<in> V" "LMap l1 f1 s (fst xo) = x"
      unfolding image_comp by auto

    obtain xo1 xo2 where Xo12 : "xo = (xo1, xo2)"
      by(cases xo; auto)

    have In : "LMap (fst_l l1) f1 s xo \<in> LMap (fst_l l1) f1 s ` V"
      using imageI[OF Xo(1)]
      by auto


    show "x <[ s1_1"
      using is_supD1[OF Sup1 In] Xo Xo12 S1
      by(auto simp add: fst_l_def prod_pleq)
  next
    fix x'
    assume Ub : "is_ub (LMap l1 f1 s ` fst ` V) x'"

    have Ub' : "is_ub (LMap (fst_l l1) f1 s ` V) (x', s1_2)"
    proof(rule is_ubI)
      fix w

      assume W : "w \<in> LMap (fst_l l1) f1 s ` V"

      then obtain wo where Wo : "wo \<in> V" "LMap (fst_l l1) f1 s wo = w"
        by auto

      obtain w1 w2 where W12 : "w = (w1, w2)"
        by(cases w; auto)

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have W1' : "w1 = LMap l1 f1 s (fst wo)"
        using Wo W12 Wo12
        by(auto simp add: fst_l_def)

      have In1 : "w1 \<in> LMap l1 f1 s ` fst ` V"
        using imageI[OF Wo(1), of "LMap l1 f1 s o fst"] 
        unfolding image_comp W1'
        by auto

      have Conc1 : "w1 <[ x'"
        using is_ubE[OF Ub In1] by auto

      have W2: "w2 = wo2"
        using Wo W12 Wo12
        by(auto simp add: fst_l_def)

      then have In2 : "w2 \<in> snd ` V"
        using imageI[OF Wo(1), of snd] W12 Wo12
        by auto
        
      have Conc2 : "w2 <[ s1_2"
        using is_supD1[OF Snd_sup In2] by auto

      show "w <[ (x', s1_2)"
        using Conc1 Conc2 W12
        by (auto simp add: prod_pleq)
    qed

    show "s1_1 <[ x'"
      using is_supD2[OF Sup1 Ub'] S1
      by(auto simp add: prod_pleq)
  qed

  have S1_1_eq : "LMap l1 f1 s s2_1 = s1_1"
    using is_sup_unique[OF So1_sup S1_1_sup] by auto

  have S2_2_sup : "is_sup (LMap l2 f2 s ` snd ` V) (s2_2)"
  proof(rule is_supI)

    fix x

    assume X: "x \<in> LMap l2 f2 s ` snd ` V"

    obtain xo where Xo : "(xo \<in> V)" "LMap l2 f2 s (snd xo) = x"
      using X unfolding image_comp
      by auto

    have Xo_in' :  "LMap (snd_l l2) f2 s xo \<in> LMap (snd_l l2) f2 s ` V "
      using imageI[OF Xo(1)]
      by fastforce

    have Conc'1 : "LMap (snd_l l2) f2 s xo <[ s2"
      using is_supD1[OF Sup2 Xo_in']
      by auto

    obtain xo1 xo2 where Xo12 : "xo = (xo1, xo2)"
      by(cases xo; auto)

    show "x <[ s2_2"
      using Conc'1 Xo S2 Xo12
      by(auto simp add: snd_l_def prod_pleq)
  next
    fix x'

    assume Ub : "is_ub (LMap l2 f2 s ` snd ` V) x'"

    have Ub' : "is_ub (LMap (snd_l l2) f2 s ` V) (s2_1, x')"
    proof(rule is_ubI)
      fix w

      assume W : "w \<in> LMap (snd_l l2) f2 s ` V "

      then obtain wo where Wo : "wo \<in> V" "LMap (snd_l l2) f2 s wo = w"
        by auto

      obtain w1 w2 where W12 : "w = (w1, w2)"
        by(cases w; auto)

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have W2' : "w2 = LMap l2 f2 s (snd wo)"
        using Wo W12 Wo12
        by(auto simp add: snd_l_def)

      have In2 : "w2 \<in> LMap l2 f2 s ` snd ` V"
        using imageI[OF Wo(1), of "LMap l2 f2 s o snd"] 
        unfolding image_comp W2'
        by auto

      have Conc1 : "w2 <[ x'"
        using is_ubE[OF Ub In2] by auto

      have W1: "w1 = wo1"
        using Wo W12 Wo12
        by(auto simp add:snd_l_def)

      then have In1 : "w1 \<in> fst ` V"
        using imageI[OF Wo(1), of fst] W12 Wo12
        by auto
        
      have Conc2 : "w1 <[ s2_1"
        using is_supD1[OF Fst_sup In1] by auto

      show "w <[ (s2_1, x')"
        using Conc1 Conc2 W12
        by (auto simp add: prod_pleq)
    qed

    show "s2_2 <[ x'"
      using is_supD2[OF Sup2 Ub'] S2
      by(auto simp add: prod_pleq)
  qed

  have S2_2_eq : "LMap l2 f2 s s1_2 = s2_2"
    using is_sup_unique[OF So2_sup S2_2_sup] by auto

  show "is_sup (LMap (snd_l l2) f2 s ` LMap (fst_l l1) f1 s ` V)
        (LMap (snd_l l2) f2 s s1)"
  proof(rule is_supI)
    fix x

    assume X: "x \<in> LMap (snd_l l2) f2 s ` LMap (fst_l l1) f1 s ` V"

    then obtain xo where Xo : "xo \<in> V" "LMap (snd_l l2) f2 s (LMap (fst_l l1) f1 s xo) = x"
      unfolding image_comp by auto

    obtain xo1 xo2 where Xo12 : "xo = (xo1, xo2)"
      by(cases xo; auto)

    obtain x1 x2 where X12 : "x = (x1, x2)"
      by(cases x; auto)

    have Eq1 : "x1 = LMap l1 f1 s xo1"
      using Xo Xo12 X12
      by(auto simp add: fst_l_def snd_l_def)

    have Xo1_in : "xo1 \<in> (fst ` V)"
      using imageI[OF Xo(1), of "fst"] Xo12 by auto

    have In1: "x1 \<in> LMap l1 f1 s ` fst ` V"
      using imageI[OF Xo1_in, of "LMap l1 f1 s "]
      unfolding image_comp Eq1
      by auto

    have Conc1 : "x1 <[ LMap l1 f1 s s2_1"
      using is_supD1[OF So1_sup In1]
      by auto

    have Conc1 : "x1 <[ s1_1"
      using is_supD1[OF S1_1_sup In1]
      by auto

    have Eq2 : "x2 = LMap l2 f2 s xo2"
      using Xo Xo12 X12
      by(auto simp add: fst_l_def snd_l_def)

    have Xo2_in : "xo2 \<in> (snd ` V)"
      using imageI[OF Xo(1), of "snd"] Xo12 by auto

    have In2 : "x2 \<in> LMap l2 f2 s ` snd ` V"
      using imageI[OF Xo2_in, of "LMap l2 f2 s"]
      unfolding image_comp Eq2
      by auto

    have Conc2 : "x2 <[ LMap l2 f2 s s1_2"
      using is_supD1[OF So2_sup In2]
      by auto

    show "x <[ LMap (snd_l l2) f2 s s1" using S1 S2 X12
      Conc1 Conc2
      by(auto simp add: snd_l_def prod_pleq)
  next
    fix x'

    assume Ub : "is_ub (LMap (snd_l l2) f2 s ` LMap (fst_l l1) f1 s ` V) x'"

    obtain x'1 x'2 where X'12 : "x' = (x'1, x'2)"
      by(cases x'; auto)

    have Eq: "LMap (snd_l l2) f2 s s1 = (s1_1, s2_2)"
      using S1 S2 S1_1_eq S2_2_eq
      by(auto simp add: snd_l_def)

    have Ub1 : "is_ub (LMap l1 f1 s ` fst ` V) x'1"
    proof(rule is_ubI)
      fix w
      assume W: "w \<in> LMap l1 f1 s ` fst ` V"

      then obtain wo where Wo : "wo \<in> V" "LMap l1 f1 s (fst wo) = w"
        unfolding image_comp by auto

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have In: "(LMap (snd_l l2) f2 s (LMap (fst_l l1) f1 s wo)) \<in> LMap (snd_l l2) f2 s ` LMap (fst_l l1) f1 s ` V "
        using imageI[OF Wo(1)] unfolding image_comp
        by auto

      have "(LMap (snd_l l2) f2 s (LMap (fst_l l1) f1 s wo)) = (w, LMap l2 f2 s wo2)"
        using Wo Wo12
        by(auto simp add: fst_l_def snd_l_def)

      then have "(w, LMap l2 f2 s wo2) <[ x'"
        using is_ubE[OF Ub In]
        by auto

      then show "w <[ x'1" using X'12
        by(auto simp add: prod_pleq)
    qed

    have Ub2 : "is_ub (LMap l2 f2 s ` snd ` V) x'2"
    proof(rule is_ubI)
      fix w
      assume W: "w \<in> LMap l2 f2 s ` snd ` V"

      then obtain wo where Wo : "wo \<in> V" "LMap l2 f2 s (snd wo) = w"
        unfolding image_comp by auto

      obtain wo1 wo2 where Wo12 : "wo = (wo1, wo2)"
        by(cases wo; auto)

      have In: "(LMap (snd_l l2) f2 s (LMap (fst_l l1) f1 s wo)) \<in> LMap (snd_l l2) f2 s ` LMap (fst_l l1) f1 s ` V "
        using imageI[OF Wo(1)] unfolding image_comp
        by auto

      have "(LMap (snd_l l2) f2 s (LMap (fst_l l1) f1 s wo)) = (LMap l1 f1 s wo1, w)"
        using Wo Wo12
        by(auto simp add: fst_l_def snd_l_def)

      then have "(LMap l1 f1 s wo1, w) <[ x'"
        using is_ubE[OF Ub In]
        by auto

      then show "w <[ x'2" using X'12
        by(auto simp add: prod_pleq)
    qed

    show "LMap (snd_l l2) f2 s s1 <[ x'"
      unfolding Eq X'12
      using is_supD2[OF S1_1_sup Ub1] is_supD2[OF S2_2_sup Ub2]
      by(auto simp add: prod_pleq)
  qed
next
  fix a1 a2 s
  fix x :: "('c * 'f)"

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
  fixes l1 :: "('a, 'b1, 'c :: {Mergeableb, Pordps}, 'f1) lifting"
  fixes S1 :: "'a \<Rightarrow> 'c1 set"
  fixes l2 :: "('a, 'b2, 'c, 'f2) lifting"
  fixes S2 :: "'a \<Rightarrow> 'c2 set"
  fixes l3 :: "('a, 'b3, 'c, 'f3) lifting"
  fixes S3 :: "'a \<Rightarrow> 'c3 set"

(* YOU ARE HERE *)

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
  fix a1_2 :: "'b * 'e"
  fix a3 :: 'g
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LUpd (merge_l l1 l2) s a1_2 (LUpd l3 s a3 b) = LUpd l3 s a3 (LUpd (merge_l l1 l2) s a1_2 b)" using A1_2
    by(auto simp add: merge_l_def orth1_3.compat orth2_3.compat)

next
  fix b :: 'c
  fix a1_2 :: "'b * 'e"
  fix a3 :: 'g
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LOut l3 s (LUpd (merge_l l1 l2) s a1_2 b) = LOut l3 s b" using A1_2
    by(auto simp add: merge_l_def orth1_3.put1_get2 orth2_3.put1_get2)
next

  fix b :: 'c
  fix a1_2 :: "'b * 'e"
  fix a3 :: 'g
  fix s

  obtain a1 a2 where A1_2 : "a1_2 = (a1, a2)"
    by(cases a1_2; auto)

  show "LOut (merge_l l1 l2) s (LUpd l3 s a3 b) = LOut (merge_l l1 l2) s b" using A1_2
    by(auto simp add: merge_l_def orth1_3.put2_get1 orth2_3.put2_get1)
next

  fix b s
  fix a1_2 :: "'b * 'e"
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
  fix a3 :: 'g

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
  fix s f1_2 f3 s1_2 s3 v
  fix V :: "'c set"

  assume Vin : "v \<in> V"
  assume Vsub1_2 : "V \<subseteq> S1 s \<inter> S2 s"
  assume Vsub3 : "V \<subseteq> S3 s"
  assume Sup1_2 : "is_sup (LMap (merge_l l1 l2) f1_2 s ` V) s1_2"
  assume Sup1_2_in : "s1_2 \<in> S1 s \<inter> S2 s \<inter> S3 s"
  assume Sup3 : "is_sup (LMap l3 f3 s ` V) s3"
  assume Sup3_in : "s3 \<in> S1 s \<inter> S2 s \<inter> S3 s"

  obtain f1 f2 where F : "f1_2 = (f1, f2)"
    by(cases f1_2; auto)

  have Vsubs : "V \<subseteq> S1 s" "V \<subseteq> S2 s" "V \<subseteq> S3 s"
    using Vsub1_2 Vsub3 by auto

  have Sup1_2' : "is_sup (LMap l1 f1 s ` LMap l2 f2 s ` V) s1_2"
    using Sup1_2
    unfolding merge_l_def F image_comp
    by(auto simp add: orth1_2.put2_get1)

  have Map3_in: "LMap l3 f3 s v \<in> LMap l3 f3 s ` V" 
    using imageI[OF Vin, of "LMap l3 f3 s"]
    by auto

  have Map3_sub : "LMap l3 f3 s ` V \<subseteq> S2 s"
  proof
    fix x
    assume X: "x \<in> LMap l3 f3 s ` V"
    then obtain xo where Xo : "xo \<in> V" "LMap l3 f3 s xo = x"
      by auto

    then have Xo' : "xo \<in> S2 s"
      using Vsubs by auto

    show "x \<in> S2 s"
      using orth2_3.put2_S1[OF Xo'] Xo(2)
      by(auto)
  qed

  have S3_in2 : "s3 \<in> S2 s"
    using Sup3_in by auto

  have Sup2_3 : "is_sup (LMap l2 f2 s ` LMap l3 f3 s ` V) (LMap l2 f2 s s3)"
    using in2.pres[OF Map3_in Map3_sub Sup3 S3_in2]
    by auto

  have Map2_3_in :
    "LMap l2 f2 s (LMap l3 f3 s v) \<in> LMap l2 f2 s ` LMap l3 f3 s ` V"
    using imageI[OF Vin]
    unfolding image_comp
    by auto

  have Map2_3_sub : "LMap l2 f2 s ` LMap l3 f3 s ` V \<subseteq> S1 s"
  proof
    fix x

    assume X : "x \<in> LMap l2 f2 s ` LMap l3 f3 s ` V "
    then obtain xo where Xo : "xo \<in> V" "LMap l2 f2 s (LMap l3 f3 s xo) = x"
      unfolding image_comp
      by auto

    then have Xo' : "xo \<in> S1 s"
      using Vsubs by auto

    show "x \<in> S1 s"
      using orth1_2.put2_S1[OF orth1_3.put2_S1[OF Xo']]
      using Xo
      by auto
  qed

  have S3_in1 : "s3 \<in> S1 s"
    using Sup3_in by auto

  have S2_3_in : "(LMap l2 f2 s s3) \<in> S1 s"
    using orth1_2.put2_S1[OF S3_in1]
    by auto

  have Conc' : "is_sup (LMap l1 f1 s ` LMap l2 f2 s ` LMap l3 f3 s ` V) (LMap l1 f1 s (LMap l2 f2 s s3))"
    using in1.pres[OF Map2_3_in Map2_3_sub Sup2_3 S2_3_in]
    by auto

  have Conc_Eq1 : "(LMap l1 f1 s (LMap l2 f2 s s3)) = LMap (merge_l l1 l2) f1_2 s s3"
    unfolding F
    by(auto simp add: merge_l_def orth1_2.put2_get1)

  have Conc_Eq2 : "(LMap (merge_l l1 l2) f1_2 s ` LMap l3 f3 s ` V) = LMap l1 f1 s ` LMap l2 f2 s ` LMap l3 f3 s ` V"
    unfolding F
    by(auto simp add: merge_l_def orth1_2.put2_get1 image_comp)

  show "is_sup (LMap (merge_l l1 l2) f1_2 s ` LMap l3 f3 s ` V) (LMap (merge_l l1 l2) f1_2 s s3)"
    using Conc' unfolding Conc_Eq1 Conc_Eq2
    by simp
next

  fix s f1_2 f3 s1_2 s3 v
  fix V :: "'c set"

  assume Vin : "v \<in> V"
  assume Vsub1_2 : "V \<subseteq> S1 s \<inter> S2 s"
  assume Vsub3 : "V \<subseteq> S3 s"
  assume Sup1_2 : "is_sup (LMap (merge_l l1 l2) f1_2 s ` V) s1_2"
  assume Sup1_2_in : "s1_2 \<in> S1 s \<inter> S2 s \<inter> S3 s"
  assume Sup3 : "is_sup (LMap l3 f3 s ` V) s3"
  assume Sup3_in : "s3 \<in> S1 s \<inter> S2 s \<inter> S3 s"

  obtain f1 f2 where F : "f1_2 = (f1, f2)"
    by(cases f1_2; auto)

  have Vsubs : "V \<subseteq> S1 s" "V \<subseteq> S2 s" "V \<subseteq> S3 s"
    using Vsub1_2 Vsub3 by auto

  have Sup1_2' : "is_sup (LMap l1 f1 s ` LMap l2 f2 s ` V) s1_2"
    using Sup1_2
    unfolding merge_l_def F image_comp
    by(auto simp add: orth1_2.put2_get1)

  have Map1_2_in: "LMap (merge_l l1 l2) f1_2 s v \<in> LMap (merge_l l1 l2) f1_2 s` V" 
    using imageI[OF Vin]
    by auto

  have Map1_2_sub : "LMap (merge_l l1 l2) f1_2 s ` V \<subseteq> S3 s"
  proof
    fix x
    assume X: "x \<in> LMap (merge_l l1 l2) f1_2 s ` V"
    then obtain xo where Xo : "xo \<in> V" "LMap (merge_l l1 l2) f1_2 s xo = x"
      by auto

    then have Xo' : "xo \<in> S3 s"
      using Vsubs by auto

    show "x \<in> S3 s"
      using orth1_3.put1_S2[OF orth2_3.put1_S2[OF Xo']] Xo(2)
      unfolding F
      by(auto simp add: merge_l_def)
  qed

  have S1_2_in3 : "s1_2 \<in> S3 s"
    using Sup1_2_in
    by auto

  show "is_sup (LMap l3 f3 s ` LMap (merge_l l1 l2) f1_2 s ` V) (LMap l3 f3 s s1_2)"
    using in3.pres[OF Map1_2_in Map1_2_sub Sup1_2 S1_2_in3]
    by auto
next
  fix a1_2 :: "'b * 'e"
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