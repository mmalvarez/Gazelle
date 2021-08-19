theory LifterX
imports Lifter Lifter_Instances
begin

(* An experiment in developing a variant of Lifter that
has a weaker notion of valid-sets (updates don't unconditionally need to be in the valid set;
instead this is only the case if we started with a valid input
*)

class Okay =
  fixes ok_S :: "'a set"

instantiation md_triv :: (_) Okay
begin
definition triv_ok_S : "(ok_S :: 'a md_triv set) = UNIV"
instance proof qed
end

instantiation md_prio :: (Okay) Okay
begin
definition prio_ok_S : "(ok_S :: 'a md_prio set) = { x :: 'a md_prio . \<exists> x' p' . x = mdp p' x' \<and> x' \<in> ok_S }"
instance proof qed
end

instantiation option :: (Okay) Okay
begin
definition option_ok_S : "(ok_S :: 'a option set) = (Some ` ok_S)"
instance proof qed
end

instantiation prod :: (Okay, Okay) Okay
begin
definition prod_ok_S : "(ok_S :: ('a * 'b) set) = { x :: 'a * 'b . \<exists> a' b' . x = (a', b') \<and> a' \<in> ok_S \<and> b' \<in> ok_S}"
instance proof qed
end

instantiation oalist :: (linorder, Okay) Okay
begin

definition oalist_ok_S :
  "(ok_S :: ('a, 'b) oalist set) = { x  :: ('a, 'b) oalist . oalist_all_val (\<lambda> y . y \<in> ok_S) x }"
instance proof qed
end

(* idea:
   - normal validity
   - valid_set has certain relation (superset) to Okay set
   - (thus, law 2 still works even if we assume Okay-ness)
   - tighter law 3: if b is in Okay, then so is LUpd l s a b.
*)
definition lifting_validx_weak ::
  "('x, 'a, 'b :: {Pord, Okay}, 'z) lifting_scheme \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validx_weak l S =
 ((lifting_valid_weak l S) \<and>
  (\<forall> s . ok_S \<subseteq> S s) \<and>
  (\<forall> s a b . b \<in> ok_S \<longrightarrow> LUpd l s a b \<in> ok_S))"

lemma lifting_validx_weakI :
  assumes HV : "lifting_valid_weak l S"
  assumes HS : "\<And> s . ok_S \<subseteq> S s"
  assumes HP' : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd l s a b \<in> ok_S"
  shows "lifting_validx_weak l S"
  using assms
  by(auto simp add: lifting_validx_weak_def)

lemma lifting_validx_weakDV :
  assumes H : "lifting_validx_weak l S"
  shows "lifting_valid_weak l S"
  using assms
  by(auto simp add: lifting_validx_weak_def)

lemma lifting_validx_weakDS :
  assumes H : "lifting_validx_weak l S"
  shows "ok_S \<subseteq> S s"
  using assms
  by(auto simp add: lifting_validx_weak_def)

lemma lifting_validx_weakDP' :
  assumes H : "lifting_validx_weak l (S :: ('a \<Rightarrow> ('b :: {Pord, Okay}) set))"
  assumes Hok : "(b :: 'b) \<in> ok_S"
  shows "LUpd l s a b \<in> ok_S"
  using assms
  by(auto simp add: lifting_validx_weak_def)

definition lifting_validx_weakb ::
  "('x, 'a, 'b :: {Pordb, Okay}, 'z) lifting_scheme \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validx_weakb l S =
 ((lifting_valid_weakb l S) \<and>
  (\<forall> s . ok_S \<subseteq> S s) \<and>
  (\<forall> s a b . b \<in> ok_S \<longrightarrow> LUpd l s a b \<in> ok_S))"

lemma lifting_validx_weakbI :
  assumes HV : "lifting_valid_weakb l S"
  assumes HS : "\<And> s . ok_S \<subseteq> S s"
  assumes HP' : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd l s a b \<in> ok_S"
  shows "lifting_validx_weakb l S"
  using assms
  by(auto simp add: lifting_validx_weakb_def)

lemma lifting_validx_weakbDV :
  assumes H : "lifting_validx_weakb l S"
  shows "lifting_valid_weakb l S"
  using assms
  by(auto simp add: lifting_validx_weakb_def)

lemma lifting_validx_weakbDS :
  assumes H : "lifting_validx_weakb l S"
  shows "ok_S \<subseteq> S s"
  using assms
  by(auto simp add: lifting_validx_weakb_def)

lemma lifting_validx_weakbDP' :
  assumes H : "lifting_validx_weakb l (S :: ('a \<Rightarrow> ('b :: {Pordb, Okay}) set))"
  assumes Hok : "(b :: 'b) \<in> ok_S"
  shows "LUpd l s a b \<in> ok_S"
  using assms
  by(auto simp add: lifting_validx_weakb_def)

definition lifting_validx ::
  "('x, 'a, 'b :: {Pord, Okay}, 'z) lifting_scheme \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validx l S =
 ((lifting_valid l S) \<and>
  (\<forall> s . ok_S \<subseteq> S s) \<and>
  (\<forall> s a b . b \<in> ok_S \<longrightarrow> LUpd l s a b \<in> ok_S))"

lemma lifting_validxI :
  assumes HV : "lifting_valid l S"
  assumes HS : "\<And> s . ok_S \<subseteq> S s"
  assumes HP' : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd l s a b \<in> ok_S"
  shows "lifting_validx l S"
  using assms
  by(auto simp add: lifting_validx_def)

lemma lifting_validxDV :
  assumes H : "lifting_validx l S"
  shows "lifting_valid l S"
  using assms
  by(auto simp add: lifting_validx_def)

lemma lifting_validxDS :
  assumes H : "lifting_validx l S"
  shows "ok_S \<subseteq> S s"
  using assms
  by(auto simp add: lifting_validx_def)

lemma lifting_validxDP' :
  assumes H : "lifting_validx l (S :: ('a \<Rightarrow> ('b :: {Pord, Okay}) set))"
  assumes Hok : "(b :: 'b) \<in> ok_S"
  shows "LUpd l s a b \<in> ok_S"
  using assms
  by(auto simp add: lifting_validx_def)

definition lifting_validxb ::
  "('x, 'a, 'b :: {Pordb, Okay}, 'z) lifting_scheme \<Rightarrow> ('x, 'b) valid_set \<Rightarrow> bool" where
"lifting_validxb l S =
 ((lifting_validb l S) \<and>
  (\<forall> s . ok_S \<subseteq> S s) \<and>
  (\<forall> s a b . b \<in> ok_S \<longrightarrow> LUpd l s a b \<in> ok_S))"

lemma lifting_validxbI :
  assumes HV : "lifting_validb l S"
  assumes HS : "\<And> s . ok_S \<subseteq> S s"
  assumes HP' : "\<And> s a b . b \<in> ok_S \<Longrightarrow> LUpd l s a b \<in> ok_S"
  shows "lifting_validxb l S"
  using assms
  by(auto simp add: lifting_validxb_def)

lemma lifting_validxbDV :
  assumes H : "lifting_validxb l S"
  shows "lifting_validb l S"
  using assms
  by(auto simp add: lifting_validxb_def)

lemma lifting_validxbDS :
  assumes H : "lifting_validxb l S"
  shows "ok_S \<subseteq> S s"
  using assms
  by(auto simp add: lifting_validxb_def)

lemma lifting_validxbDP' :
  assumes H : "lifting_validxb l (S :: ('a \<Rightarrow> ('b :: {Pordb, Okay}) set))"
  assumes Hok : "(b :: 'b) \<in> ok_S"
  shows "LUpd l s a b \<in> ok_S"
  using assms
  by(auto simp add: lifting_validxb_def)

(* Problem: how does this affect the first law (LOut (LUpd ...))
we might be able to keep this the same. However, I can't get over the fact that this
feels wrong...
*)

lemma triv_l_validx_weak :
  shows "lifting_validx_weak (triv_l :: ('x, 'a :: Bogus, 'a md_triv) lifting) (\<lambda> _ . UNIV)"
proof(rule lifting_validx_weakI)
  show "lifting_valid_weak' triv_l" using triv_l_valid_weak by auto
next
  fix s
  show "ok_S \<subseteq> UNIV" using triv_ok_S
    by(auto)
next
  show "\<And>s a b. b \<in> ok_S \<Longrightarrow> LUpd triv_l s a b \<in> ok_S"
    by(auto simp add: triv_ok_S)
qed

lemma option_l_validx_weak :
  assumes H : "lifting_validx_weak (t :: ('x, 'a, 'b :: {Pord, Okay}, 'z) lifting_scheme) S"
  shows "lifting_validx_weak (option_l t) (option_l_S S)"
proof(rule lifting_validx_weakI)
  show "lifting_valid_weak (option_l t)
     (option_l_S S)"
    using option_l_valid_weak lifting_validx_weakDV[OF H] by auto
next
  show "\<And> s . ok_S \<subseteq> option_l_S S s"
    using lifting_validx_weakDS[OF H]
    by(auto simp add: option_l_S_def option_ok_S)
next
  show "\<And>s a b.
       b \<in> ok_S \<Longrightarrow>
       LUpd (option_l t) s a b \<in> ok_S"
    using lifting_validx_weakDP'[OF H]
    by(auto simp add: option_l_def option_l_S_def option_ok_S)
qed

(* TODO: option_l_valid, option_l_validb *)

lemma fst_l_validx_weak :
  assumes H : "lifting_validx_weak (t :: ('x, 'a, 'b :: {Pord, Okay}, 'z) lifting_scheme) S"
  shows "lifting_validx_weak (fst_l t) (fst_l_S S)"
proof(rule lifting_validx_weakI)
  show "lifting_valid_weak (fst_l t) (fst_l_S S)"
    using lifting_validx_weakDV[OF H] fst_l_valid_weak by auto
next
  show "\<And>s. ok_S \<subseteq> fst_l_S S s"
    using lifting_validx_weakDS[OF H]
    by(auto simp add: fst_l_S_def prod_ok_S)
next
  show "\<And>s a b.
         b \<in> ok_S \<Longrightarrow> LUpd (fst_l t) s a b \<in> ok_S"
    using lifting_validx_weakDP'[OF H]
    by(auto simp add: fst_l_def fst_l_S_def prod_ok_S)
qed

(* TODO: other variants of fst; snd as well *)

lemma merge_l_validx_gen :
  assumes H1 : "lifting_validx (l1 :: ('x, 'a1, 'b :: {Mergeable, Okay}, 'z1) lifting_scheme) S1"
  assumes H2 : "lifting_validx (l2 :: ('x, 'a2, 'b :: {Mergeable, Okay}, 'z2) lifting_scheme) S2"
  assumes Hort : "l_ortho_alt l1 S1 l2 S2"
  shows "lifting_validx (merge_l l1 l2) (\<lambda> s . S1 s \<inter> S2 s)"
proof(rule lifting_validxI)
  show "lifting_valid (merge_l l1 l2) (\<lambda>s. S1 s \<inter> S2 s)"
    using merge_l_valid_gen[OF lifting_validxDV[OF H1] lifting_validxDV[OF H2] Hort]
    by auto
next
  show "\<And> s . ok_S \<subseteq> S1 s \<inter> S2 s"
    using lifting_validxDS[OF H1] lifting_validxDS[OF H2]
      prod_ok_S
    by(auto)
next
  show "\<And>s a b.
       b \<in> ok_S \<Longrightarrow>
       LUpd (merge_l l1 l2) s a b \<in> ok_S"
    using lifting_validxDP'[OF H1] lifting_validxDP'[OF H2]
    by(auto simp add: merge_l_def)
qed





end